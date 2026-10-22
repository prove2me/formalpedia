-- Prove2me | Theorems.Thm_QMCProduct_HalfApprox_eq_7
-- name    : QMCProduct.HalfApprox.eq_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:50:01.208139+00:00
-- url     : https://prove2.me/theorems/ff9a47f9-cc07-4f12-821b-ab5da0dddd8e
-- title:
--   Equation (7), p. 17 — expected QMC edge energy of Gaussian product-state rounding is (1 + F(3, vij))/4
-- statement:
--   Let $\widetilde\rho$ be a level-2 pseudo-density, let $i\ne j$, and let $W_i$ be unit rounding vectors whose pairwise Gram values are $-v_{ij}$. Apply Algorithm 2 using three independent standard Gaussian rows and call its random product state $\rho$. Then
--   $$\mathbb E\operatorname{Tr}(H_{ij}\rho)=\frac{1-F(3,-v_{ij})}{4}=\frac{1+F(3,v_{ij})}{4}.$$
--   The second equality uses the oddness of $F(3,\cdot)$. This is the edge formula used for vertices rounded in Algorithm 4.
--
--   **Formalization Note** The expectation is a Bochner integral over the Gaussian law. This item states equation (7) for Algorithm 2's full product state; the Algorithm 4 edge marginal agrees on $B$.
-- source:
--   Parekh & Thompson, An Optimal Product-State Approximation for 2-Local Quantum Hamiltonians with Positive Terms, arXiv:2206.08342v2, p. 17, equation (7)

import Definitions.Def_QMCProduct_HalfApprox_Algorithm

set_option autoImplicit false

namespace QMCProduct.HalfApprox

open MeasureTheory

/-- Equation (7), p. 17, for the product state of Algorithm 2. -/
theorem eq_7 {n d : ℕ} (ρt : Op n) (hρ : IsPseudoDensity 2 ρt)
    (W : Fin n → EuclideanSpace ℝ (Fin d)) (hW : IsRoundingInput ρt W)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R : Fin 3 → Fin d → Ω → ℝ) (hR : IsStdGaussianMatrix P R)
    (i j : Fin n) (hij : i ≠ j) :
    (∫ ω, (hQMC i j * alg2State W R ω).trace.re ∂P) =
        (1 - F 3 (-v ρt i j)) / 4 ∧
    (1 - F 3 (-v ρt i j)) / 4 = (1 + F 3 (v ρt i j)) / 4 := by sorry

end QMCProduct.HalfApprox
