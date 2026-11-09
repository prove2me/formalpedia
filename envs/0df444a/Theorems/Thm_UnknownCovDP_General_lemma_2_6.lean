-- Prove2me | Theorems.Thm_UnknownCovDP_General_lemma_2_6
-- name    : UnknownCovDP.General.lemma_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:11:48.541308+00:00
-- url     : https://prove2.me/theorems/0c19a7b8-8199-488f-9840-931f114574e7
-- title:
--   Lemma 2.6 — OUT case upper bound (corrected: $k\ge C\max(1,n\log n)$)
-- statement:
--   For every $c\in(0,1)$ there is $C>0$ such that for all $d,k$, all $n\ge1$, all $y\in\mathbb R^d$ and all positive semidefinite $\Sigma$: if $k\ge C\max(1,n\log n)$, then
--   $$\Pr_{z\sim N(0,\Sigma)}\Bigl[T_{\Sigma,y}(z)\ge\frac{k}{4n}\Bigr]\le\frac cn.$$
--   A fresh point, independent of $y$, rarely scores high on the test.
--
--   Differences from the source:
--   - correction: hypothesis k ≥ C n log n → hypothesis k ≥ C max(1, n log n); reason: false as printed at n = 1: with c = 1/2, any C, n = 1, d = 1, Σ = (1), y = (1), k = 1, the hypothesis holds since log 1 = 0, and T(z) = z² gives Pr[z² ≥ 1/4] ≈ 0.617 > 1/2 = c/n; for n ≥ 2, n log n ≥ 2 log 2 > 1, so the corrected hypothesis is the printed one
--   - encoding: n ∈ ℕ a sample size, with c/n in the statement → hypothesis 1 ≤ n; reason: c/n is undefined at n = 0
-- source:
--   Gaucher, Linder, Smith, Ullman, Zakynthinou, Dimension-Free Private Mean Estimation is Impossible Without the Covariance, STOC 2027 submission #573 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/573.pdf, Lemma 2.6, printed p. 13 (PDF p. 14)

import Mathlib
import Definitions.Def_UnknownCovDP_General_TestEvents

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace UnknownCovDP.General

/-- Lemma 2.6 (OUT case upper bound), printed p. 13, PDF p. 14, with the hypothesis
`k ≥ C n log n` corrected to `k ≥ C max(1, n log n)` (the two coincide for `n ≥ 2`; the printed
statement fails at `n = 1`). For every `c ∈ (0,1)` there is `C > 0` such that for all `y` and all
`S ⪰ 0`, `Pr_{z∼N(0,S)}[T_{S,y}(z) ≥ k/(4n)] ≤ c/n`. -/
theorem lemma_2_6 (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d k n : ℕ) (y : Vec d) (S : Mat d), S.PosSemidef → 1 ≤ n →
      C * max 1 ((n : ℝ) * Real.log n) ≤ k →
      multivariateGaussian (0 : Vec d) S {z | (k : ℝ) / (4 * n) ≤ testStat S y z} ≤
        ENNReal.ofReal (c / n) := by sorry

end UnknownCovDP.General
