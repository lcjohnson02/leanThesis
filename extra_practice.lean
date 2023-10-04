import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib

variable (R : Type*) [Ring R]


theorem self_sub (a : R) : a - a = 0 := by
  rw [sub_self]
  done

theorem pos_square (a : ℝ) : a ≠ 0 → a^2 > 0 := by
  intro h1
  by_cases h2 : a > 0
  have h3 : a * a > 0 := by
    apply Real.mul_pos h2 h2
    done
  rw [sq]
  apply h3
  rw [sq]
  push_neg at h2
  have h3 : a < 0 := by
    apply Ne.lt_of_le h1 h2

  done

#check sq
#check PosNum
#check Real.mul_pos
#check by_cases
#check sq_pos_iff
#check mul_self_pos
#check mul_one
#check one_mul
#check neg_mul_neg
#check sq
#check neg_one_sq
#check Ne.lt_of_le
#check mul_one_div



example (a b c d : ℝ) (h1: a < b) (h2 : c ≤ d) : a + c < b + d := by
  by_cases h3 : c = d
  rw [h3]
  apply add_lt_add_right h1
  push_neg at h3
  have h4 : c < d := by
    apply Ne.lt_of_le h3 h2
  apply add_lt_add h1 h4
  done


example (a b : ℝ) (h1 : ∀ ε : ℝ, ε > 0 → a ≤ b + ε) : a ≤ b := by
  by_contra h2
  push_neg at h2
  let ε := (a - b) / 2
  have h3 : ε > 0 := by
    refine half_pos ?h
    exact Iff.mpr sub_pos h2
    done
  have h4 : a ≤ b + ε := by
    apply h1
    apply h3
    done
  dsimp at h4
  linarith
  done

theorem mulByNegOne (a : ℝ) : -1 * a = -a := by
  calc
    -1 * a = 0 + (-1 * a) := by rw [zero_add (-1 * a)]
    _ = -a + a + (-1 * a) := by
      ring
    _ = -a + (1 * a) + (-1 * a) := by ring
    _ = -a + (1 + (-1)) * a := by
      ring
    _ = -a + 0 * a := by ring
    _ = -a := by ring
  done

theorem onesNeg : (1 : ℝ) = (-1) * (-1) := by
  calc
    (1 : ℝ) = 1 + 0 := by rw [add_zero]
    _ = 1 + 0 * (-1) := by rw [zero_mul]
    _ = 1 + (1 + (-1)) * (-1) := by ring
    _ = 1 + 1 * (-1) + (-1) * (-1) := by ring
    _ = 1 + (-1) + (-1) * (-1) := by ring --rw [← mulByNegOne 1]
    _ = (-1) * (-1) := by ring
  done

example : ∀ a b : ℝ, a < 0 ∧ b < 0 → a * b > 0 := by
  intro a b h1
  have h2 : a < 0 := h1.left
  have h3 : b < 0 := h1.right
  have h4 : a * b = 1 * (a * b) := by
    linarith
    done
  have h5 : (-1) * (-1) = (1 : ℝ)  := by
    rw [← onesNeg]
    done
  rw [h4]
  rw [←h5]
  have h6 : -1 * -1 * (a * b) = -1 * a * -1 * b := by
    ring
    done
  rw [h6]
  have h7 : -1 * a * -1 * b = (-1 * a) * (-1 * b) := by
    ring
    done
  rw [h7]
  rw [mulByNegOne, mulByNegOne]
  apply mul_pos
  -- Showing -a is positive
  exact Iff.mpr neg_pos h2
  -- Showing -b is positive
  exact Iff.mpr neg_pos h3
  done


def ArchPropNat (a : ℝ) :=
  ∃ k, k > a


def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε


theorem Distribute (n : ℝ) : 2 * (n + 1) = 2 * n + 2 := by
  exact mul_add_one 2 n
  done

example : ConvergesTo (fun (n : ℕ) ↦ ((2 * n) / (n + 1))) 2 := by
  intro ε
  intro h1
  obtain ⟨k, h13⟩ := exists_nat_gt (2 / ε - 1) --Archimedean Propert
  use k
  intro n
  intro h2
  dsimp
  have h3 : (2 : ℝ) = 2 * ((n + 1) / (n + 1)) := by
    have h4 : ((n + 1) / (n + 1)) = (n + 1) * ((n + 1) : ℝ)⁻¹ := by
      rfl
      done
    rw [h4]
    have h5 : (n + 1) * ((n + 1) : ℝ)⁻¹ = 1 := by
      rw [mul_inv_cancel]
      exact Nat.cast_add_one_ne_zero n
      done
    rw [h5]
    exact Eq.symm (mul_one 2)
    done
  nth_rewrite 2 [h3]
  have h6 : 2 * ((↑n + 1) : ℝ) / (↑n + 1) = ((2 * n) + 2) / (n + 1) := by
    rw [Distribute n]
    done
  have h7 : 2 * (((↑n + 1) : ℝ) / (↑n + 1)) = 2 * (↑n + 1) / (↑n + 1) := by
    rw [← mul_div_assoc 2 ((n + 1) : ℝ) ((n + 1) : ℝ)]
    done
  rw [h7]
  rw [h6]
  rw [div_sub_div_same (2 * n : ℝ) (2 * n + 2) (n + 1)]
  rw [sub_add_cancel']
  rw [abs_div]
  simp
  have h8 : |(↑n + 1 : ℝ)| = ↑n + 1 := by
    simp
    apply LT.lt.le (Nat.cast_add_one_pos ↑n)
    done
  rw [h8]
  have h9 : (2 : ℝ) / (↑n + 1) ≤ 2 / (k + 1) := by
    apply div_le_div_of_le_left
    · --case 1
      linarith
      done
    · --case 2
      exact Nat.cast_add_one_pos k
      done
    · --case 3
      convert add_le_add_right h2 1
      apply Iff.intro
      · --subcase 1
        exact fun a => Nat.add_le_add_right h2 1
        done
      · --subcase 2
        intro h14
        apply add_le_add_right
        exact Iff.mpr Nat.cast_le h2
        done
      done
    done
  have h10 : 2 / (k + 1) < 2 / (2 / ε - 1 + 1) := by
    apply div_lt_div_of_lt_left
    · --case 1
      linarith
      done
    · --case 2
      simp
      apply div_pos
      linarith
      apply h1
      done
    · --case 3
      convert add_le_add_right h2 1
      apply Iff.intro
      · --subcase 1
        intro h11
        exact Nat.add_le_add_right h2 1
        done
      · --subcase 2
        intro h11
        have h12 : 2 / ε - 1 < (k : ℝ) := by
          simp only []
          apply h13
          done
        exact add_lt_add_right h12 1
        done
      done
    done
  calc
    2 / (↑n + 1) ≤ (2 : ℝ) / (k + 1) := by
      apply h9
      done
    _ < (2 : ℝ) / (2 / ε - 1 + 1) := by
      apply h10
      done
    _ = ε := by
      ring_nf
      apply inv_inv
      done
  done



example : ConvergesTo (s1 : ℕ → ℝ) (0 : ℝ) ↔
    ConvergesTo (abs s1 : ℕ → ℝ) (0 : ℝ) := by
  rw [ConvergesTo]
  rw [ConvergesTo]
  have h3 (x : ℕ): |s1 x| = |abs s1 x| := by
    have h4 : |abs s1 x| = |(|s1 x|)| := by
      exact rfl
      done
    rw [h4]
    rw [abs_abs]
    done
  apply Iff.intro
  intro h1
  simp
  simp at h1
  simp_rw [← h3]
  apply h1
  intro h1
  simp
  simp at h1
  simp_rw [h3]
  apply h1
  done

#check round_ofNat
#check Nat.ceil
#check abs
#check abs_abs
#check mul_inv_cancel
#check mul_inv_self
#check mul_div_assoc
#check div_sub_div_same
#check add_sub_assoc
#check sub_add_cancel'
#check abs_div
#check abs_neg
#check Nat.cast_add_one_pos
#check le_of_lt
#check div_lt_div_of_lt_left
#check div_pos
#check Int.le_add_one
#check add_le_add_right
#check add_le_add
#check Nat.le_ceil
#check Nat.lt_ceil
#check Int.lt_ceil
#check Real.ceil_logb_nat_cast
#check Nat.ceil_add_one
#check Nat.ceil_lt_add_one
#check exists_nat_gt
