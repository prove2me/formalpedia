-- Prove2me | Theorems.Thm_VarStorageQN_LeastChange_hsNorm_ideal
-- name    : VarStorageQN.LeastChange.hsNorm_ideal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:46:31.042422+00:00
-- url     : https://prove2.me/theorems/5881ae22-43d3-4310-b6ff-814baed1b99d
-- title:
--   Annex p. 26 — operator norm bound and Hilbert–Schmidt ideal property
-- statement:
--   Let $A,B$ be bounded operators on a real Hilbert space. For any Hilbert–Schmidt $A$,
--
--   $$\|A\|_{\mathrm{op}}\le\|A\|_{\mathrm{HS}}.$$
--
--   If either $A$ or $B$ is Hilbert–Schmidt, their composition $AB$ is Hilbert–Schmidt. This ideal property ensures the weighted perturbations in (A.4) and (A.6) have a valid Hilbert–Schmidt norm.
--
--   **Formalization Note** Membership is tested against an arbitrary Hilbert basis; the separate basis-independence milestone identifies the result with the paper's basis-free class.
-- source:
--   Gilbert & Lemaréchal, Some numerical experiments with variable-storage quasi-Newton algorithms, IIASA Working Paper WP-88-121 (August 1988), p. 26, Annex, paragraph after (A.1)

import Mathlib
import Definitions.Def_VarStorageQN_LeastChange_HilbertSchmidt

namespace VarStorageQN.LeastChange

open InnerProductSpace ContinuousLinearMap
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Annex, p. 26: the operator norm bound and the two-sided ideal property. -/
theorem hsNorm_ideal {ι : Type*} (b : HilbertBasis ι ℝ H) :
    (∀ A : H →L[ℝ] H, HSSummable b A → ‖A‖ ≤ hsNorm b A) ∧
    (∀ A B : H →L[ℝ] H,
      (HSSummable b A ∨ HSSummable b B) → HSSummable b (A ∘L B)) := by sorry

end VarStorageQN.LeastChange
