-- Prove2me | Theorems.Thm_VBSDP_Duality_compl_slackness
-- name    : VBSDP.Duality.compl_slackness
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:52:27.475281+00:00
-- url     : https://prove2.me/theorems/b305d87e-6922-4a9a-891b-2e4d1e98401d
-- title:
--   Complementary slackness for an optimal primal–dual pair
-- statement:
--   Suppose $x$ is primal feasible, $Z$ is dual feasible, and their objective values agree: $c^Tx=-\operatorname{Tr}(F_0Z)$. Then
--
--   $$ZF(x)=0.$$
--
--   Feasibility and equality of objective values make both points optimal, so this is the paper’s complementary slackness condition.
--
--   This statement supplies a target in the duality development.
--
--   **Formalization Note** Matrices have dimension $n\times n$, with coefficients $F_1,\ldots,F_m$ indexed in Lean from 0 and $F_0$ passed separately. Positive semidefiniteness and positive definiteness are matrix conditions; trace is the matrix trace.
-- source:
--   Vandenberghe and Boyd, Semidefinite Programming, SIAM Review 38(1) (1996), p. 65, complementary slackness, PDF p. 17, https://doi.org/10.1137/1038003

import Mathlib
import Definitions.Def_VBSDP_Duality_IsPrimalFeasible
import Definitions.Def_VBSDP_Duality_IsDualFeasible

namespace VBSDP.Duality

theorem compl_slackness {m n : ℕ} (c : Fin m → ℝ)
    (F₀ : Matrix (Fin n) (Fin n) ℝ) (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (x : Fin m → ℝ) (Z : Matrix (Fin n) (Fin n) ℝ)
    (hx : IsPrimalFeasible F₀ F x) (hZ : IsDualFeasible F c Z)
    (hopt : c ⬝ᵥ x = -(F₀ * Z).trace) :
    Z * lmi F₀ F x = 0 := by sorry

end VBSDP.Duality
