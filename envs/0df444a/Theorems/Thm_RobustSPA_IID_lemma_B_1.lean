-- Prove2me | Theorems.Thm_RobustSPA_IID_lemma_B_1
-- name    : RobustSPA.IID.lemma_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:13:54.25699+00:00
-- url     : https://prove2.me/theorems/f12c9cad-d714-4f97-b208-250bed7e12a0
-- title:
--   Lemma B-1, p. App-4 — integration by parts of h against a distribution G on [0,1], split at r*
-- statement:
--   Let $r \in [0,1]$, let $h$ be continuous on $[0,1]$ and differentiable on $(0,1)$ except perhaps at $v = r$, with derivative $h'$ integrable on $[0,1]$, and let $G$ be a probability distribution supported on $[0,1]$, with CDF $G(t) = G((-\infty,t])$. Then
--   $$\int_{[0,1]} h(v)\,dG(v) = h(0)G(r) + \int_0^{r} h'(v)\big(G(r) - G(v)\big)dv + h(r)\big(G(1) - G(r)\big) + \int_{r}^1 h'(v)\big(G(1) - G(v)\big)dv.$$
--
--   This identity converts an expectation under $G$ into integrals against the CDF of $G$; it computes the first term $\mathbb E[v^{(1)} - v^{(1)}\Phi(v^{(1)})]$ of the regret of $\mathrm{SPA}(\Phi)$ in the proof of Proposition 1.
--
--   **Formalization Note.** The page assumes "differentiable everywhere except perhaps at $v = r^*$". The paper applies the lemma to $h(v) = v - v\Phi(v)$, which has a kink at $v = 1$ as well, so differentiability is required only on the open interval $(0,1)$ minus $r$; integrability of $h'$ is added because the proof starts from $h(v) = h(0) + \int_0^v h'$, which needs it.
-- source:
--   Anunrojwong, Balseiro & Besbes, On the Robustness of Second-Price Auctions in Prior-Independent Mechanism Design, arXiv:2204.10478v5, p. App-4 (PDF p. 34), Lemma B-1

import Mathlib
import Definitions.Def_RobustSPA_IID_Setting

namespace RobustSPA.IID

open MeasureTheory

/-- Lemma B-1 (p. App-4). Let `h` be continuous on `[0,1]`, differentiable on `(0,1)` except
perhaps at `r ∈ [0,1]`, with integrable derivative `h'`, and let `G` be a distribution on `[0,1]`.
Then `∫_{[0,1]} h dG = h(0)G(r) + ∫_0^r h'(v)(G(r) − G(v)) dv + h(r)(G(1) − G(r))
+ ∫_r^1 h'(v)(G(1) − G(v)) dv`. -/
theorem lemma_B_1 (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1) (h h' : ℝ → ℝ)
    (hcont : ContinuousOn h (Set.Icc 0 1))
    (hderiv : ∀ v ∈ Set.Ioo (0 : ℝ) 1, v ≠ r → HasDerivAt h (h' v) v)
    (hint : IntervalIntegrable h' MeasureTheory.volume 0 1)
    (G : ProbabilityMeasure ℝ) (hG : (G : Measure ℝ) (Set.Icc 0 1)ᶜ = 0) :
    ∫ v in Set.Icc (0 : ℝ) 1, h v ∂(G : Measure ℝ) =
      h 0 * cdfOf G r + ∫ v in (0 : ℝ)..r, h' v * (cdfOf G r - cdfOf G v) +
        h r * (cdfOf G 1 - cdfOf G r) + ∫ v in r..1, h' v * (cdfOf G 1 - cdfOf G v) := by sorry

end RobustSPA.IID
