-- Prove2me | Theorems.Thm_TDApprox_Sampling_mean_recursion
-- name    : TDApprox.Sampling.mean_recursion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:24:34.560242+00:00
-- url     : https://prove2.me/theorems/53272fb6-6676-495d-9898-57abfc077033
-- title:
--   §9, p. 25 — mean recurrence for q-sampled TD(0)
-- statement:
--   Let the state–successor pairs be independent across iterations, with joint law $q(i)p_{ij}$. If the transition costs and basis functions are bounded, the parameter vectors have finite expectations and their means obey
--
--   $$\mathbb E[r_{t+1}]=\mathbb E[r_t]+\gamma_t\bigl(\Phi Q\bar g+\Phi Q(\alpha P\Phi^{\mathsf T}-\Phi^{\mathsf T})\mathbb E[r_t]\bigr).$$
--
--   Here $Q$ has diagonal $q(i)$ and $\bar g(i)=\sum_jp_{ij}g(i,j)$. This is the general mean recurrence that is specialized in the counterexample.
--
--   **Formalization Note** Boundedness makes every integral and weighted series well-defined on countable $S$. The displayed formula corrects the page's $j_{t+1}$ in the first line and its placement of $\bar g$ inside a matrix factor multiplying the mean in the second line.
-- source:
--   Tsitsiklis & Van Roy, LIDS-P-2322 (1996), Theorem 3 proof, p. 25, mean recursion; https://dspace.mit.edu/entities/publication/ab395d25-a6d3-407a-9589-60eaac58fd05

import Mathlib
import Definitions.Def_TDApprox_Sampling_Model

namespace TDApprox.Sampling

open MeasureTheory ProbabilityTheory

theorem mean_recursion
    {S Ω : Type*} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : S → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq : HasSum q 1)
    (P : Kernel S S) [IsMarkovKernel P] (I J : ℕ → Ω → S)
    (hsample : IsQSample μ q P I J)
    (K : ℕ)
    (g : S → S → ℝ) (φ : S → Fin K → ℝ)
    (hg : ∃ Bg : ℝ, ∀ i j, |g i j| ≤ Bg)
    (hφ : ∃ Bφ : ℝ, ∀ i k, |φ i k| ≤ Bφ)
    (α : ℝ) (γ : ℕ → ℝ) (r₀ : Fin K → ℝ) :
    ∀ t,
      Integrable (fun ω => qIter α γ g φ r₀ I J t ω) μ ∧
      ∫ ω, qIter α γ g φ r₀ I J (t + 1) ω ∂μ =
        (∫ ω, qIter α γ g φ r₀ I J t ω ∂μ) +
          (γ t) • (qBias q P g φ +
            Matrix.mulVec (qDrift q P α φ)
              (∫ ω, qIter α γ g φ r₀ I J t ω ∂μ)) := by sorry

end TDApprox.Sampling
