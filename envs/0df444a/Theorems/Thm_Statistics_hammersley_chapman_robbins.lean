-- Prove2me | Theorems.Thm_Statistics_hammersley_chapman_robbins
-- name    : Statistics.hammersley_chapman_robbins
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T23:54:53.867905+00:00
-- url     : https://prove2.me/theorems/40548226-02c5-4da5-a494-b26ff68fd4d0
-- title:
--   Hammersley–Chapman–Robbins variance bound
-- statement:
--   **The Hammersley–Chapman–Robbins bound.** Let $\mu$ be a probability measure and let $L \in L^2(\mu)$ satisfy $\mathbb{E}_\mu[L] = 1$, so that $L$ is the density $\mathrm{d}\nu/\mathrm{d}\mu$ of an alternative probability law $\nu \ll \mu$ with finite $\chi^2$-divergence. For any statistic $\delta \in L^2(\mu)$,
--   $$\bigl(\mathbb{E}_\nu[\delta] - \mathbb{E}_\mu[\delta]\bigr)^2 \;\le\; \operatorname{Var}_\mu(\delta)\; \chi^2(\nu \,\|\, \mu),\qquad \chi^2(\nu \,\|\, \mu) = \mathbb{E}_\mu\bigl[(L-1)^2\bigr],$$
--   where $\mathbb{E}_\nu[\delta]$ is written as $\mathbb{E}_\mu[\delta L]$. Taking the supremum over alternatives $\nu$ in a model gives a lower bound on the variance of any estimator that is unbiased across the model — the two-point (Chapman–Robbins) form of the Cramér–Rao inequality, which needs no differentiability or regularity assumptions at all.
-- source:
--   J. M. Hammersley, On estimating restricted parameters, J. Roy. Statist. Soc. Ser. B 12 (1950), 192-240; D. G. Chapman and H. Robbins, Minimum variance estimation without regularity assumptions, Ann. Math. Statist. 22 (1951), 581-586, Section 2, eq. (2).

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Probability.Moments.Variance

open MeasureTheory
open scoped ENNReal NNReal

theorem Statistics.hammersley_chapman_robbins {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (δ L : Ω → ℝ)
    (hδ : MemLp δ 2 μ) (hL : MemLp L 2 μ) (hL1 : ∫ ω, L ω ∂μ = 1) :
    (∫ ω, δ ω * L ω ∂μ - ∫ ω, δ ω ∂μ) ^ 2
      ≤ (∫ ω, (δ ω - ∫ ω', δ ω' ∂μ) ^ 2 ∂μ) * (∫ ω, (L ω - 1) ^ 2 ∂μ) := by sorry
