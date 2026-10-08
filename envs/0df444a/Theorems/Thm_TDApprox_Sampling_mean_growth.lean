-- Prove2me | Theorems.Thm_TDApprox_Sampling_mean_growth
-- name    : TDApprox.Sampling.mean_growth
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:24:46.912097+00:00
-- url     : https://prove2.me/theorems/520cfcf1-6000-49c3-a6e3-da714d456d60
-- title:
--   §9, p. 25 — unbounded growth of the expected parameter
-- statement:
--   Use the paper's zero-cost one-feature construction, assume $q(s_1)>0$, $q(s_2)\le q(s_1)$ and $p(s_2)>5/(6\alpha)$, and let the step sizes satisfy Assumption 4. With $\varepsilon=6\alpha p(s_2)-5$, the expected parameter vectors are well-defined and satisfy
--
--   $$\lvert\mathbb E[r_{t+1}]\rvert\ge(1+\gamma_t\varepsilon q(s_1))\lvert\mathbb E[r_t]\rvert,\qquad \lim_{t\to\infty}\lVert\mathbb E[r_t]\rVert=\infty\quad(r_0\ne0).$$
--
--   This supplies the final growth step in the proof of Theorem 3.
--
--   **Formalization Note** The one-dimensional parameter is represented by `Fin 1 → ℝ`; the growth inequality uses its sole coordinate while the limit uses the function-space norm.
-- source:
--   Tsitsiklis & Van Roy, LIDS-P-2322 (1996), Theorem 3 proof, p. 25, final display; https://dspace.mit.edu/entities/publication/ab395d25-a6d3-407a-9589-60eaac58fd05

import Mathlib
import Definitions.Def_TDApprox_Sampling_Model

namespace TDApprox.Sampling

open MeasureTheory ProbabilityTheory Filter

theorem mean_growth
    {S Ω : Type*} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s₁ s₂ : S) (hne : s₁ ≠ s₂)
    (p : Measure S) [IsProbabilityMeasure p] (hp : ∀ i, 0 < p {i})
    (q : S → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq : HasSum q 1)
    (hq₁ : 0 < q s₁) (hqle : q s₂ ≤ q s₁)
    (I J : ℕ → Ω → S) (hsample : IsQSample μ q (rowKernel p) I J)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (hp₂ : 5 / (6 * α) < (p {s₂}).toReal)
    (γ : ℕ → ℝ) (hγ : TDApprox.Conv.Assumption4 γ)
    (r₀ : Fin 1 → ℝ) (hr₀ : r₀ ≠ 0) :
    let φ := sampleFeature s₁ s₂
    let ε := 6 * α * (p {s₂}).toReal - 5
    (∀ t, Integrable (fun ω => qIter α γ (fun _ _ => 0) φ r₀ I J t ω) μ) ∧
    (∀ t, (1 + γ t * ε * q s₁) *
        |(∫ ω, qIter α γ (fun _ _ => 0) φ r₀ I J t ω ∂μ) (0 : Fin 1)| ≤
      |(∫ ω, qIter α γ (fun _ _ => 0) φ r₀ I J (t + 1) ω ∂μ) (0 : Fin 1)|) ∧
    Tendsto (fun t => ‖∫ ω, qIter α γ (fun _ _ => 0) φ r₀ I J t ω ∂μ‖)
      atTop atTop := by sorry

end TDApprox.Sampling
