-- Prove2me | Theorems.Thm_QMCProduct_HalfApprox_lemma_5
-- name    : QMCProduct.HalfApprox.lemma_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:49:07.123708+00:00
-- url     : https://prove2.me/theorems/e1bb15d3-5d4a-4662-9780-7e61305bcd56
-- title:
--   Lemma 5, p. 17 — for k ≥ 2, µij ∈ [0, 1], vij ∈ [−1/3, 1] and sij ∈ [−1, 1]
-- statement:
--   Let $\widetilde\rho$ be a $k$-positive pseudo-density on $n$ qubits, with $k\ge2$, and let $i\ne j$. For the QMC edge values $\mu_{ij},v_{ij},s_{ij}$ of Definition 12,
--   $$\mu_{ij}\in[0,1],\qquad v_{ij}\in[-1/3,1],\qquad s_{ij}\in[-1,1].$$
--   These intervals delimit the feasible edge values used in the rounding and monogamy analysis.
--
--   **Formalization Note** Distinct sites are explicit because an edge has distinct endpoints.
-- source:
--   Parekh & Thompson, An Optimal Product-State Approximation for 2-Local Quantum Hamiltonians with Positive Terms, arXiv:2206.08342v2, p. 17, Lemma 5

import Definitions.Def_QMCProduct_HalfApprox_Basic

set_option autoImplicit false

namespace QMCProduct.HalfApprox

/-- Lemma 5, p. 17. -/
theorem lemma_5 {n k : ℕ} (hk : 2 ≤ k) (ρt : Op n)
    (hρ : IsPseudoDensity k ρt) (i j : Fin n) (hij : i ≠ j) :
    (0 ≤ mu ρt i j ∧ mu ρt i j ≤ 1) ∧
    (-(1 / 3 : ℝ) ≤ v ρt i j ∧ v ρt i j ≤ 1) ∧
    (-1 ≤ s ρt i j ∧ s ρt i j ≤ 1) := by sorry

end QMCProduct.HalfApprox
