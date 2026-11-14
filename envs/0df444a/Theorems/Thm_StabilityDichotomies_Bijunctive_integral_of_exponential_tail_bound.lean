-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_integral_of_exponential_tail_bound
-- name    : StabilityDichotomies.Bijunctive.integral_of_exponential_tail_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:13:24.345989+00:00
-- url     : https://prove2.me/theorems/1fcb3146-2b49-45ad-97b4-db812c240a60
-- title:
--   An exponential tail bound gives a logarithmic expectation bound
-- statement:
--   Let $X$ be an integrable nonnegative random variable on a probability space. If $\Pr[X>t]\le q e^{-\beta t}$ for all $t\ge0$, with $q\ge1$ and $\beta>0$, then $\mathbb E[X]\le(\log q+1)/\beta$. This supplies the logarithmic expectation estimate used for the maximum shift, once its integrability is established.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, graph-deletion sensitivity step.

import Mathlib
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter

theorem StabilityDichotomies.Bijunctive.integral_of_exponential_tail_bound {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : Integrable f μ) (hnonneg : ∀ᵐ ω ∂μ, 0 ≤ f ω)
    (q β : ℝ) (hq : 1 ≤ q) (hβ : 0 < β)
    (htail : ∀ t : ℝ, 0 ≤ t → μ.real {ω | t < f ω} ≤ q * Real.exp (-β*t)) :
    (∫ ω, f ω ∂μ) ≤ (Real.log q + 1) / β := by
  sorry
