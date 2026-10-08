-- Prove2me | Theorems.Thm_VBSDP_Duality_weak_duality_values
-- name    : VBSDP.Duality.weak_duality_values
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:54:47.453818+00:00
-- url     : https://prove2.me/theorems/362e2d31-15e4-4e3a-b085-11582853103a
-- title:
--   Weak duality of optimal values
-- statement:
--   For the optimal values of the primal semidefinite program (1) and its dual (27),
--
--   $$d^*\le p^*.$$
--
--   The inequality also includes empty feasible sets and unbounded objectives under the extended-real conventions.
--
--   This statement supplies a target in the duality development.
--
--   **Formalization Note** Matrices have dimension $n\times n$, with coefficients $F_1,\ldots,F_m$ indexed in Lean from 0 and $F_0$ passed separately. Positive semidefiniteness and positive definiteness are matrix conditions; trace is the matrix trace.
-- source:
--   Vandenberghe and Boyd, Semidefinite Programming, SIAM Review 38(1) (1996), p. 64, sentence following definition of d*, PDF p. 16, https://doi.org/10.1137/1038003

import Mathlib
import Definitions.Def_VBSDP_Duality_pStar
import Definitions.Def_VBSDP_Duality_dStar

namespace VBSDP.Duality

theorem weak_duality_values {m n : ℕ} (c : Fin m → ℝ)
    (F₀ : Matrix (Fin n) (Fin n) ℝ) (F : Fin m → Matrix (Fin n) (Fin n) ℝ) :
    dStar c F₀ F ≤ pStar c F₀ F := by sorry

end VBSDP.Duality
