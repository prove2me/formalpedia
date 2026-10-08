-- Prove2me | Theorems.Thm_VBSDP_Duality_eq_30
-- name    : VBSDP.Duality.eq_30
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:52:09.886738+00:00
-- url     : https://prove2.me/theorems/5cfc1f3f-a742-4f57-a525-acf23edab3d3
-- title:
--   Equation (30): the primal–dual gap identity
-- statement:
--   Let $x$ be primal feasible and $Z$ dual feasible for (1) and (27). Then
--
--   $$c^Tx+\operatorname{Tr}(ZF_0)=\operatorname{Tr}(ZF(x))\ge0.$$
--
--   This identifies the duality gap with the trace pairing of two positive semidefinite matrices.
--
--   This statement supplies a target in the duality development.
--
--   **Formalization Note** Matrices have dimension $n\times n$, with coefficients $F_1,\ldots,F_m$ indexed in Lean from 0 and $F_0$ passed separately. Positive semidefiniteness and positive definiteness are matrix conditions; trace is the matrix trace.
-- source:
--   Vandenberghe and Boyd, Semidefinite Programming, SIAM Review 38(1) (1996), p. 64, equation (30), PDF p. 16, https://doi.org/10.1137/1038003

import Mathlib
import Definitions.Def_VBSDP_Duality_IsPrimalFeasible
import Definitions.Def_VBSDP_Duality_IsDualFeasible

namespace VBSDP.Duality

theorem eq_30 {m n : ℕ} (c : Fin m → ℝ) (F₀ : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin m → Matrix (Fin n) (Fin n) ℝ) (x : Fin m → ℝ)
    (Z : Matrix (Fin n) (Fin n) ℝ)
    (hx : IsPrimalFeasible F₀ F x) (hZ : IsDualFeasible F c Z) :
    c ⬝ᵥ x + (Z * F₀).trace = (∑ i, (Z * F i).trace * x i) + (Z * F₀).trace ∧
      (∑ i, (Z * F i).trace * x i) + (Z * F₀).trace =
        (Z * lmi F₀ F x).trace ∧
      0 ≤ (Z * lmi F₀ F x).trace := by sorry

end VBSDP.Duality
