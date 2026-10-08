-- Prove2me | Theorems.Thm_StochKriging_Unbiased_theorem_1
-- name    : StochKriging.Unbiased.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:07:38.308839+00:00
-- url     : https://prove2.me/theorems/cbc59238-47ee-40ac-aeeb-09eebff8bd94
-- title:
--   Theorem 1 — the plug-in stochastic kriging predictor (13) is unbiased under Assumption 1
-- statement:
--   Consider the stochastic kriging model $\mathcal Y_j(\mathbf x)=\beta_0+\mathsf M(\mathbf x)+\varepsilon_j(\mathbf x)$ on $\mathbb R^d$, with distinct design points $\mathbf x_1,\dots,\mathbf x_k$, replication counts $n_i\ge2$ and noise variances $\mathsf V(\mathbf x_i)>0$. Let $\bar{\mathcal Y}$ be the vector of sample means, $\widehat{\mathsf V}(\mathbf x_i)=\mathcal S^2(\mathbf x_i)$ the sample variances of the same replications,
--   $$\widehat\Sigma_\varepsilon=\mathrm{Diag}\big\{\widehat{\mathsf V}(\mathbf x_1)/n_1,\dots,\widehat{\mathsf V}(\mathbf x_k)/n_k\big\},$$
--   and define, for any point $\mathbf x_0\in\mathbb R^d$ (simulated or not),
--   $$\widehat{\widehat{\mathsf Y}}(\mathbf x_0)=\beta_0+\Sigma_{\mathsf M}(\mathbf x_0,\cdot)^\top\big[\Sigma_{\mathsf M}+\widehat\Sigma_\varepsilon\big]^{-1}\big(\bar{\mathcal Y}-\beta_0\mathbf 1_k\big).\tag{13}$$
--   If Assumption 1 holds, then the prediction error $\widehat{\widehat{\mathsf Y}}(\mathbf x_0)-\mathsf Y(\mathbf x_0)$, where $\mathsf Y(\mathbf x_0)=\beta_0+\mathsf M(\mathbf x_0)$, is integrable and
--   $$\mathrm E\Big[\widehat{\widehat{\mathsf Y}}(\mathbf x_0)-\mathsf Y(\mathbf x_0)\Big]=0.$$
--
--   Estimating the intrinsic variance from the replications, and plugging it into the stochastic kriging predictor, therefore introduces no prediction bias; the price of estimation is paid only in mean squared error.
--
--   **Formalization Note** Integrability of the error is stated explicitly, because a Bochner integral of a non-integrable function is $0$ in Lean. $\Sigma_{\mathsf M}$ and $\Sigma_{\mathsf M}(\mathbf x_0,\cdot)$ are the true covariances of the field; the inverse is `Matrix.inv`, which is a genuine inverse here because Assumption 1 makes $\Sigma_{\mathsf M}$ positive definite and $\widehat\Sigma_\varepsilon$ is positive semidefinite. $\mathbf x_0$ may coincide with a design point.
-- source:
--   Ankenman, Nelson, Staum, Stochastic Kriging for Simulation Metamodeling, Proc. 2008 Winter Simulation Conference, p. 366, Theorem 1

import Mathlib
import Definitions.Def_StochKriging_Unbiased_Model
import Definitions.Def_StochKriging_Unbiased_Predictor

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace StochKriging.Unbiased

/-- Theorem 1 (p. 366): under Assumption 1, the plug-in stochastic kriging predictor (13) is
unbiased for `Y(x₀) = β₀ + M(x₀)`: `E[Ŷ̂(x₀) − Y(x₀)] = 0` (the error is integrable). -/
theorem theorem_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d k : ℕ} (x : Fin k → EuclideanSpace ℝ (Fin d)) (hx : Function.Injective x)
    (n : Fin k → ℕ) (hn : ∀ i, 2 ≤ n i) (β₀ : ℝ) (V : EuclideanSpace ℝ (Fin d) → ℝ≥0)
    (hV : ∀ i, 0 < V (x i)) (M : EuclideanSpace ℝ (Fin d) → Ω → ℝ)
    (ε : ℕ → EuclideanSpace ℝ (Fin d) → Ω → ℝ) (hA : Assumption1 P M ε V x)
    (x₀ : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun ω => predictorHat P β₀ M ε x n x₀ ω - (β₀ + M x₀ ω)) P ∧
      ∫ ω, (predictorHat P β₀ M ε x n x₀ ω - (β₀ + M x₀ ω)) ∂P = 0 := by sorry

end StochKriging.Unbiased
