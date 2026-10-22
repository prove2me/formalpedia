-- Prove2me | Theorems.Thm_QMCProduct_HalfApprox_fact_1
-- name    : QMCProduct.HalfApprox.fact_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:50:12.458279+00:00
-- url     : https://prove2.me/theorems/61dd9630-0db3-4b86-8fa3-aeb40e839b2a
-- title:
--   Fact 1, p. 16 — if vij ≤ γ, product-state rounding has approximation factor ≥ 1/2 on ij
-- statement:
--   Let $\widetilde\rho$ be a level-2 pseudo-density for a Quantum Max Cut graph. Use the paper's threshold $\gamma=0.911$. If an edge $ij$ has both endpoints in $B$, so its relaxed value satisfies $v_{ij}\le\gamma$, then Algorithm 4's Gaussian product-state rounding has expected edge energy at least half the relaxed edge value:
--   $$\mathbb E\operatorname{Tr}(H_{ij}\rho_{\mathrm{Alg4}})\ge\frac12\mu_{ij}.$$
--   This supplies the per-edge guarantee for the class $E(B)$.
--
--   **Formalization Note** The rounding vectors have the Gram values of the level-2 solution, and Gaussian entries are independent standard normals. Both endpoints belong to $B$, which is the case in Algorithm 4 where the paper applies Fact 1. The energy is computed from equation (5)'s full output matrix.
-- source:
--   Parekh & Thompson, An Optimal Product-State Approximation for 2-Local Quantum Hamiltonians with Positive Terms, arXiv:2206.08342v2, p. 16, Fact 1; application in proof of Theorem 3 p. 19

import Definitions.Def_QMCProduct_HalfApprox_Algorithm

set_option autoImplicit false

namespace QMCProduct.HalfApprox

open MeasureTheory

/-- Fact 1, p. 16, for an edge whose endpoints are rounded in B. -/
theorem fact_1 {n d : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ρt : Op n) (hρ : IsPseudoDensity 2 ρt)
    (W : Fin n → EuclideanSpace ℝ (Fin d)) (hW : IsRoundingInput ρt W)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R : Fin 3 → Fin d → Ω → ℝ) (hR : IsStdGaussianMatrix P R)
    (i j : Fin n) (hij : G.Adj i j)
    (hi : inB G ρt (911 / 1000 : ℝ) i)
    (hj : inB G ρt (911 / 1000 : ℝ) j) :
    (1 / 2 : ℝ) * mu ρt i j ≤
      ∫ ω, (hQMC i j * alg4State G ρt (911 / 1000 : ℝ) W R ω).trace.re ∂P := by sorry

end QMCProduct.HalfApprox
