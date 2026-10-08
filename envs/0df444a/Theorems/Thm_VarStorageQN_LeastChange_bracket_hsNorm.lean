-- Prove2me | Theorems.Thm_VarStorageQN_LeastChange_bracket_hsNorm
-- name    : VarStorageQN.LeastChange.bracket_hsNorm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:46:29.68126+00:00
-- url     : https://prove2.me/theorems/fa3e4ece-c29e-42c1-b9e9-a046655dad91
-- title:
--   Equation (A.2) — Hilbert–Schmidt and operator norms of a bracket
-- statement:
--   For vectors $u,v$ in a real Hilbert space, the bracket operator $[u,v]d=\langle v,d\rangle u$ is Hilbert–Schmidt and satisfies
--
--   $$\|[u,v]\|_{\mathrm{HS}}=\|[u,v]\|_{\mathrm{op}}=\|u\|\,\|v\|. $$
--
--   This rank-one identity supplies the size of the update terms in the Annex.
--
--   **Formalization Note** The Hilbert–Schmidt claim uses any Hilbert basis. Mathlib provides the operator-norm identity for `rankOne`; the square-sum identity remains part of this milestone.
-- source:
--   Gilbert & Lemaréchal, Some numerical experiments with variable-storage quasi-Newton algorithms, IIASA Working Paper WP-88-121 (August 1988), p. 26, Annex, (A.2)

import Mathlib
import Definitions.Def_VarStorageQN_LeastChange_HilbertSchmidt
import Definitions.Def_VarStorageQN_LeastChange_Bracket

namespace VarStorageQN.LeastChange

open InnerProductSpace ContinuousLinearMap
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Display (A.2), p. 26, including Hilbert–Schmidt membership. -/
theorem bracket_hsNorm {ι : Type*} (b : HilbertBasis ι ℝ H) (u v : H) :
    HSSummable b (bracket u v) ∧
    hsNorm b (bracket u v) = ‖bracket u v‖ ∧
    ‖bracket u v‖ = ‖u‖ * ‖v‖ := by sorry

end VarStorageQN.LeastChange
