-- Prove2me | Theorems.Thm_WeightedMajority_Continuous_lemma_5_2
-- name    : WeightedMajority.Continuous.lemma_5_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:19:31.105984+00:00
-- url     : https://prove2.me/theorems/0fdf46d4-16bf-4f64-a631-ac65bed22509
-- title:
--   Lemma 5.2 — logarithmic potential bound for continuous predictions
-- statement:
--   Consider a finite, nonempty pool with positive initial weights, nonnegative weights thereafter, $0\le\beta<1$, and expert predictions and labels in $[0,1]$. At each trial $j$, suppose every weight obeys the upper update bound $w_i^{(j+1)}\le w_i^{(j)}[1-(1-\beta)|x_i^{(j)}-\rho^{(j)}|]$. Let $\gamma^{(j)}$ be the weighted mean prediction and let $w_{\mathrm{init}}$ and $w_{\mathrm{fin}}$ be the initial and final total weights.
--
--   If $\beta=0$ and $|\gamma^{(j)}-\rho^{(j)}|=1$ on some trial, then $w_{\mathrm{fin}}=0$. When $w_{\mathrm{fin}}>0$,
--
--   $$\ln\frac{w_{\mathrm{fin}}}{w_{\mathrm{init}}}\le\sum_j\ln\bigl(1-(1-\beta)|\gamma^{(j)}-\rho^{(j)}|\bigr).$$
--
--   This is the paper's potential estimate for the master prediction; it uses only the upper update bound, so it also applies to WMC runs.
--
--   **Formalization Note** The paper treats a zero final weight as a $-\infty$ logarithmic bound. Lean's real logarithm of zero returns zero, so the finite logarithmic clause explicitly assumes $w_{\mathrm{fin}}>0$.
-- source:
--   Littlestone and Warmuth, The Weighted Majority Algorithm, Information and Computation 108 (1994), p. 234, Lemma 5.2; https://doi.org/10.1006/inco.1994.1009

import Definitions.Def_WeightedMajority_Continuous_WMCRun

namespace WeightedMajority.Continuous

/-- Lemma 5.2, p. 234: a unit master loss at beta zero exhausts the weights;
otherwise the logarithmic potential is bounded by the trialwise factors. -/
theorem lemma_5_2 {n t : ℕ} (beta : ℝ) (w : ℕ → Fin n → ℝ)
    (x : Fin t → Fin n → ℝ) (rho : Fin t → ℝ)
    (h : PotentialConditions beta w x rho) :
    (beta = 0 → (∃ j : Fin t, |meanPrediction w x j - rho j| = 1) →
      WeightedMajority.Basic.totalWeight w t = 0) ∧
    (0 < WeightedMajority.Basic.totalWeight w t →
      Real.log (WeightedMajority.Basic.totalWeight w t / WeightedMajority.Basic.totalWeight w 0) ≤
        ∑ j : Fin t,
          Real.log (1 - (1 - beta) * |meanPrediction w x j - rho j|)) := by sorry

end WeightedMajority.Continuous
