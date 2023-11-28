import Mathlib

-- Simple Function
def adding (n1 : Nat) (n2 : Nat) : Nat :=
  n1 + n2

-- Simple Theorem
example (x : α) (A : Set α) (B : Set α) (h1 : A ⊆ B)
    (h2 : x ∈ A) : x ∈ B := by
  apply h1
  apply h2
  done


-- Inequality Addition
example (a b c d : ℝ) (h1: a < b)
    (h2 : c ≤ d) : a + c < b + d := by
  by_cases h3 : c = d
  rw [h3]
  apply add_lt_add_right h1
  push_neg at h3
  have h4 : c < d := by
    apply Ne.lt_of_le h3 h2
  exact calc
    a + c < b + c := add_lt_add_right h1 c
    _ < b + d := add_lt_add_left h4 b
  done

-- a is Less Than or Equal to b
example (a b : ℝ) (h1 : ∀ ε : ℝ,
    ε > 0 → a ≤ b + ε) :
    a ≤ b := by
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

-- Absolute Convergence
example (s1 : ℕ → ℝ) :
    ConvergesTo s1 (0 : ℝ) ↔
    ConvergesTo (abs s1) (0 : ℝ)
    := by
  rw [ConvergesTo]
  rw [ConvergesTo]
  have h3 (x : ℕ) : |s1 x| =
      |abs s1 x| := by
    simp [abs]
    done
  apply Iff.intro
  · --Forwards
    intro h1
    simp
    simp at h1
    simp [← h3]
    apply h1
  · --Reverse
    intro h1
    simp
    simp at h1
    simp_rw [h3]
    apply h1
  done

-- Convergence of a Specific Sequence
example : ConvergesTo (fun (n : ℕ) ↦
    ((2 * n) / (n + 1))) 2 := by
  intro ε
  intro h1
  obtain ⟨k, h13⟩ :=
    exists_nat_gt (2 / ε - 1) --Archimedean Property
  use k
  intro n
  intro h2
  dsimp
  have h3 : (2 : ℝ) = 2 * ((n + 1) / (n + 1)) := by
    have h4 : ((n + 1) / (n + 1)) =
        (n + 1) * ((n + 1) : ℝ)⁻¹ := by
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
  have h6 : 2 * ((↑n + 1) : ℝ) / (↑n + 1) =
      ((2 * n) + 2) / (n + 1) := by
    rw [Distribute n]
    done
  have h7 : 2 * (((↑n + 1) : ℝ) / (↑n + 1)) =
      2 * (↑n + 1) / (↑n + 1) := by
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
