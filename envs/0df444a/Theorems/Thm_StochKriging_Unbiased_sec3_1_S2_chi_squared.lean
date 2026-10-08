-- Prove2me | Theorems.Thm_StochKriging_Unbiased_sec3_1_S2_chi_squared
-- name    : StochKriging.Unbiased.sec3_1_S2_chi_squared
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:06:47.707702+00:00
-- url     : https://prove2.me/theorems/6930fabd-82a2-4d5f-8d52-05160c811540
-- title:
--   §3.1, p. 365 — under Assumption 1, S²(x_i) has a scaled chi-squared distribution
-- statement:
--   In the stochastic kriging model $\mathcal Y_j(\mathbf x)=\beta_0+\mathsf M(\mathbf x)+\varepsilon_j(\mathbf x)$ with distinct design points $\mathbf x_1,\dots,\mathbf x_k$, replication counts $n_i\ge2$ and noise variances $\mathsf V(\mathbf x_i)>0$, suppose Assumption 1 holds, and let $\mathcal S^2(\mathbf x_i)$ be the sample variance (12) of the $n_i$ outputs at $\mathbf x_i$. Then $\mathcal S^2(\mathbf x_i)$ has a scaled chi-squared distribution:
--   $$\frac{(n_i-1)\,\mathcal S^2(\mathbf x_i)}{\mathsf V(\mathbf x_i)}\sim\chi^2_{n_i-1}.$$
--
--   The scaling is the one the paper uses on p. 366 for the estimator $\widehat{\mathsf V}$ ("$(n-1)\widehat{\mathsf V}/\mathsf V$ has a chi-squared distribution"). The distribution of $\mathcal S^2$ governs how much estimating the intrinsic variance inflates the prediction error.
--
--   **Formalization Note** $\chi^2_\nu$ is Mathlib's `gammaMeasure (ν/2) (1/2)` (shape $\nu/2$, rate $1/2$), and "has distribution" is `HasLaw`, which includes almost-everywhere measurability.
-- source:
--   Ankenman, Nelson, Staum, Stochastic Kriging for Simulation Metamodeling, Proc. 2008 Winter Simulation Conference, p. 365, §3.1, sentence after display (12) (second conjunct); scaling as glossed on p. 366

import Mathlib
import Definitions.Def_StochKriging_Unbiased_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace StochKriging.Unbiased

/-- §3.1, p. 365 (second conjunct): under Assumption 1, `𝒮²(xᵢ)` has a scaled chi-squared
distribution: `(nᵢ − 1) 𝒮²(xᵢ) / V(xᵢ) ∼ χ²_{nᵢ−1}`, the gamma law with shape `(nᵢ − 1)/2` and
rate `1/2`. -/
theorem sec3_1_S2_chi_squared {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {d k : ℕ} (x : Fin k → EuclideanSpace ℝ (Fin d))
    (hx : Function.Injective x) (n : Fin k → ℕ) (hn : ∀ i, 2 ≤ n i) (β₀ : ℝ)
    (V : EuclideanSpace ℝ (Fin d) → ℝ≥0) (hV : ∀ i, 0 < V (x i))
    (M : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (ε : ℕ → EuclideanSpace ℝ (Fin d) → Ω → ℝ)
    (hA : Assumption1 P M ε V x) (i : Fin k) :
    HasLaw (fun ω => ((n i : ℝ) - 1) * S2 β₀ M ε x n ω i / (V (x i) : ℝ))
      (gammaMeasure (((n i : ℝ) - 1) / 2) (1 / 2)) P := by sorry

end StochKriging.Unbiased
