-- Prove2me | Theorems.Thm_VarStorageQN_LeastChange_bracket_comp
-- name    : VarStorageQN.LeastChange.bracket_comp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:46:32.498131+00:00
-- url     : https://prove2.me/theorems/32d8e84d-7d5e-4560-ba55-bfcb9fefc726
-- title:
--   Annex p. 27 — composition identities for bracket operators
-- statement:
--   For every bounded operator $R$ and vectors $u,v$ on a real Hilbert space,
--
--   $$R[u,v]=[Ru,v],\qquad [u,v]R=[u,R^*v].$$
--
--   The formulas identify how a bracket changes under left or right composition and are used with the weighted updates.
--
--   **Formalization Note** `bracket u v` has the paper's argument order. Mathlib provides the left-composition rank-one identity; both identities are stated here as the source gives them.
-- source:
--   Gilbert & Lemaréchal, Some numerical experiments with variable-storage quasi-Newton algorithms, IIASA Working Paper WP-88-121 (August 1988), p. 27, Annex, first paragraph

import Mathlib
import Definitions.Def_VarStorageQN_LeastChange_HilbertSchmidt
import Definitions.Def_VarStorageQN_LeastChange_Bracket

namespace VarStorageQN.LeastChange

open InnerProductSpace ContinuousLinearMap
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Annex, p. 27: the two bracket identities involving an adjoint. -/
theorem bracket_comp (R : H →L[ℝ] H) (u v : H) :
    R ∘L bracket u v = bracket (R u) v ∧
    bracket u v ∘L R = bracket u (adjoint R v) := by sorry

end VarStorageQN.LeastChange
