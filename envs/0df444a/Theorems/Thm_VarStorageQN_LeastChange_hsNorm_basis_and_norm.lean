-- Prove2me | Theorems.Thm_VarStorageQN_LeastChange_hsNorm_basis_and_norm
-- name    : VarStorageQN.LeastChange.hsNorm_basis_and_norm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:46:29.113416+00:00
-- url     : https://prove2.me/theorems/d1202a25-be59-42b2-be97-f0abf7940113
-- title:
--   Annex after (A.1) — basis independence and Hilbert–Schmidt norm axioms
-- statement:
--   Let $A$ be a bounded operator on a real Hilbert space. For any two orthonormal bases $b=(e_i)$ and $b'=(f_j)$, the family $(\|Ae_i\|^2)$ is summable exactly when $(\|Af_j\|^2)$ is, and, when it is summable,
--
--   $$\sum_i\|Ae_i\|^2=\sum_j\|Af_j\|^2.$$
--
--   For each basis $b$, the Hilbert–Schmidt operators contain zero, are closed under addition and real scalar multiplication, and satisfy nonnegativity, definiteness, homogeneity, and the triangle inequality for $\|\cdot\|_{\mathrm{HS}}$. Thus (A.1) defines a basis-independent norm on the Hilbert–Schmidt class.
--
--   **Formalization Note** The basis index types are arbitrary, so the claim covers nonseparable spaces. Norm assertions are restricted to `HSSummable` operators to avoid the default value of a nonsummable real sum.
-- source:
--   Gilbert & Lemaréchal, Some numerical experiments with variable-storage quasi-Newton algorithms, IIASA Working Paper WP-88-121 (August 1988), p. 26, Annex, paragraph after (A.1)

import Mathlib
import Definitions.Def_VarStorageQN_LeastChange_HilbertSchmidt

namespace VarStorageQN.LeastChange

open InnerProductSpace ContinuousLinearMap
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Annex, after (A.1), p. 26: basis independence and norm axioms on Hilbert–Schmidt operators. -/
theorem hsNorm_basis_and_norm {ι : Type*} (b : HilbertBasis ι ℝ H) :
    (∀ {κ : Type*} (b' : HilbertBasis κ ℝ H) (A : H →L[ℝ] H),
      (HSSummable b A ↔ HSSummable b' A) ∧
      (HSSummable b A → (∑' i, ‖A (b i)‖ ^ 2) = (∑' j, ‖A (b' j)‖ ^ 2))) ∧
    HSSummable b (0 : H →L[ℝ] H) ∧
    (∀ A B : H →L[ℝ] H, HSSummable b A → HSSummable b B →
      HSSummable b (A + B) ∧ hsNorm b (A + B) ≤ hsNorm b A + hsNorm b B) ∧
    (∀ (a : ℝ) (A : H →L[ℝ] H), HSSummable b A →
      HSSummable b (a • A) ∧ hsNorm b (a • A) = |a| * hsNorm b A) ∧
    (∀ A : H →L[ℝ] H, HSSummable b A →
      0 ≤ hsNorm b A ∧ (hsNorm b A = 0 ↔ A = 0)) := by sorry

end VarStorageQN.LeastChange
