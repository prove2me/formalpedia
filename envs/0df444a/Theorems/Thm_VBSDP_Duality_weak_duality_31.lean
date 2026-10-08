-- Prove2me | Theorems.Thm_VBSDP_Duality_weak_duality_31
-- name    : VBSDP.Duality.weak_duality_31
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:52:10.053975+00:00
-- url     : https://prove2.me/theorems/693a48e0-21a1-4172-8eb8-d10d4dbfcf0c
-- title:
--   Equation (31): weak duality
-- statement:
--   For every primal feasible $x$ and dual feasible $Z$,
--
--   $$-\operatorname{Tr}(F_0Z)\le c^Tx.$$
--
--   Every dual feasible objective value therefore bounds every primal feasible objective value from below.
--
--   This statement supplies a target in the duality development.
--
--   **Formalization Note** Matrices have dimension $n\times n$, with coefficients $F_1,\ldots,F_m$ indexed in Lean from 0 and $F_0$ passed separately. Positive semidefiniteness and positive definiteness are matrix conditions; trace is the matrix trace.
-- source:
--   Vandenberghe and Boyd, Semidefinite Programming, SIAM Review 38(1) (1996), p. 64, equation (31), PDF p. 16, https://doi.org/10.1137/1038003

import Mathlib
import Definitions.Def_VBSDP_Duality_IsPrimalFeasible
import Definitions.Def_VBSDP_Duality_IsDualFeasible

namespace VBSDP.Duality

theorem weak_duality_31 {m n : ℕ} (c : Fin m → ℝ)
    (F₀ : Matrix (Fin n) (Fin n) ℝ) (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (x : Fin m → ℝ) (Z : Matrix (Fin n) (Fin n) ℝ)
    (hx : IsPrimalFeasible F₀ F x) (hZ : IsDualFeasible F c Z) :
    -(F₀ * Z).trace ≤ c ⬝ᵥ x := by sorry

end VBSDP.Duality
