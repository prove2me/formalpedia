-- Prove2me | Theorems.Thm_QMCProduct_HalfApprox_theorem_3
-- name    : QMCProduct.HalfApprox.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:50:10.218993+00:00
-- url     : https://prove2.me/theorems/833e0d48-715e-4e22-8a5f-f9765b227f3e
-- title:
--   Theorem 3, p. 17 — for some γ ∈ (−1/3, 1], Algorithm 4 is a 1/2-approximation for Quantum Max Cut
-- statement:
--   There is a fixed threshold $\gamma\in(-1/3,1]$ such that, for every finite nonnegatively weighted Quantum Max Cut instance $H$, Algorithm 4 run on an optimal level-2 quantum Lasserre solution $\widetilde\rho$ outputs a density matrix $\rho$ for every Gaussian draw, and its expected energy obeys
--   $$\mathbb E\operatorname{Tr}(H\rho)\ge\frac12\lambda_{\max}(H).$$
--   The threshold is chosen before the instance. The bound compares the algorithm with the best unrestricted quantum state, even though its output is a mixture of product states.
--
--   **Formalization Note** Lean expresses $\lambda_{\max}(H)$ by comparison with $\operatorname{Tr}(H\sigma)$ for every density matrix $\sigma$, since the maximum is attained at a top eigenvector. The expectation is over the Gaussian matrix only. Rounding vectors are supplied with the exact Gram matrix constructed by the paper's level-2 solution. Weights are nonnegative on the counted undirected edges. The polynomial running-time clause of Definition 5 is not formalized.
-- source:
--   Parekh & Thompson, An Optimal Product-State Approximation for 2-Local Quantum Hamiltonians with Positive Terms, arXiv:2206.08342v2, p. 17, Theorem 3; Algorithm 4 p. 14; Definition 5 p. 7

import Definitions.Def_QMCProduct_HalfApprox_Algorithm

set_option autoImplicit false

namespace QMCProduct.HalfApprox

open MeasureTheory

/-- Theorem 3, p. 17: Algorithm 4 has approximation ratio one half. -/
theorem theorem_3 : ∃ γ : ℝ, -(1 / 3 : ℝ) < γ ∧ γ ≤ 1 ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (w : Fin n → Fin n → ℝ),
      (∀ e ∈ edges G, 0 ≤ w e.1 e.2) →
      ∀ ρt : Op n, IsOptimalL2 (qmcHamiltonian G w) ρt →
      ∀ (d : ℕ) (W : Fin n → EuclideanSpace ℝ (Fin d)),
        IsRoundingInput ρt W →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (R : Fin 3 → Fin d → Ω → ℝ),
        IsStdGaussianMatrix P R →
        (∀ ω, QAlgorithms.IsDensityMatrix (alg4State G ρt γ W R ω)) ∧
        ∀ σ : Op n, QAlgorithms.IsDensityMatrix σ →
          (1 / 2 : ℝ) * (qmcHamiltonian G w * σ).trace.re ≤
            ∫ ω, (qmcHamiltonian G w * alg4State G ρt γ W R ω).trace.re ∂P := by sorry

end QMCProduct.HalfApprox
