-- Prove2me | Theorems.Thm_StochKriging_Unbiased_sec3_multivariate_normal
-- name    : StochKriging.Unbiased.sec3_multivariate_normal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:06:54.075772+00:00
-- url     : https://prove2.me/theorems/ffa57e2b-b677-4646-b5df-7b214d2eb7b2
-- title:
--   §3, p. 365 — under Assumption 1, (Y(x₀), Ȳ(x₁), …, Ȳ(x_k)) is multivariate normal
-- statement:
--   Consider the stochastic kriging model $\mathcal Y_j(\mathbf x)=\beta_0+\mathsf M(\mathbf x)+\varepsilon_j(\mathbf x)$ with distinct design points $\mathbf x_1,\dots,\mathbf x_k\in\mathbb R^d$, replication counts $n_i\ge1$, and noise variances $\mathsf V(\mathbf x_i)>0$, and suppose Assumption 1 holds. Let $\bar{\mathcal Y}(\mathbf x_i)$ be the sample mean of the $n_i$ outputs at $\mathbf x_i$ and $\mathsf Y(\mathbf x_0)=\beta_0+\mathsf M(\mathbf x_0)$ the noise-free response at an arbitrary point $\mathbf x_0$. Then the random vector
--   $$\big(\mathsf Y(\mathbf x_0),\ \bar{\mathcal Y}(\mathbf x_1),\ \dots,\ \bar{\mathcal Y}(\mathbf x_k)\big)$$
--   has a multivariate normal distribution.
--
--   Joint normality of the target and the sample means is what makes the stochastic kriging predictor a conditional expectation, and it is the first ingredient in the analysis of the plug-in predictor (13).
--
--   **Formalization Note** The vector is a random element of `ℝ × (Fin k → ℝ)` and "multivariate normal" is Mathlib's `HasGaussianLaw` (every continuous linear functional of it is a real Gaussian, degenerate ones included). This item formalizes only the first clause of the paper's sentence; the conditional-expectation clause is not stated here.
-- source:
--   Ankenman, Nelson, Staum, Stochastic Kriging for Simulation Metamodeling, Proc. 2008 Winter Simulation Conference, p. 365, §3, paragraph after Assumption 1 (first clause)

import Mathlib
import Definitions.Def_StochKriging_Unbiased_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace StochKriging.Unbiased

/-- §3, p. 365 (first clause): under Assumption 1, `(Y(x₀), 𝒴̄(x₁), …, 𝒴̄(x_k))` is
multivariate normal, where `Y(x₀) = β₀ + M(x₀)`. -/
theorem sec3_multivariate_normal {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {d k : ℕ} (x : Fin k → EuclideanSpace ℝ (Fin d))
    (hx : Function.Injective x) (n : Fin k → ℕ) (hn : ∀ i, 1 ≤ n i) (β₀ : ℝ)
    (V : EuclideanSpace ℝ (Fin d) → ℝ≥0) (hV : ∀ i, 0 < V (x i))
    (M : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (ε : ℕ → EuclideanSpace ℝ (Fin d) → Ω → ℝ)
    (hA : Assumption1 P M ε V x) (x₀ : EuclideanSpace ℝ (Fin d)) :
    HasGaussianLaw (fun ω => (β₀ + M x₀ ω, Ybar β₀ M ε x n ω)) P := by sorry

end StochKriging.Unbiased
