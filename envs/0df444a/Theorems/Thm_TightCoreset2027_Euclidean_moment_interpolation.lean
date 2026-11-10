-- Prove2me | Theorems.Thm_TightCoreset2027_Euclidean_moment_interpolation
-- name    : TightCoreset2027.Euclidean.moment_interpolation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T06:06:03.649685+00:00
-- url     : https://prove2.me/theorems/b1b9c1a2-7971-49b2-b1aa-c039740e0dee
-- title:
--   Lemma 2.4 — moment interpolation
-- statement:
--   Let $Y$ be a measurable real-valued random variable on any probability space. Suppose its fourth absolute moment is integrable and strictly positive, so $0<\mathbb E|Y|^4<\infty$. Then
--
--   $$\mathbb E|Y|\ge\frac{(\mathbb E|Y|^2)^{3/2}}{(\mathbb E|Y|^4)^{1/2}}.$$
--
--   This moment inequality is the probability-space statement used in the projection discrepancy estimate. No boundedness or finite-support restriction is imposed on $Y$. Integrability of the lower moments follows from the fourth-moment hypothesis and the probability normalization.
--
--   Differences from the source:
--   - encoding: a real random variable with 0 < E|Y|^4 < infinity → an arbitrary probability measure, measurable Y, integrable fourth power, and positive fourth integral; reason: these explicitly encode the meaning of random variable and finite moment and exclude the default integral on nonintegrable inputs
-- source:
--   Junqiu Hu, Lingxiao Huang, Jian Li, Baoduo Xu, STOC 2027 submission #879 (October 2026), Lemma 2.4, printed p. 18 / PDF p. 20; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/879.pdf

import Mathlib
open MeasureTheory
set_option autoImplicit false

namespace TightCoreset2027.Euclidean

theorem moment_interpolation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (hY : Measurable Y)
    (hfour : Integrable (fun ω => |Y ω| ^ 4) μ)
    (hpos : 0 < ∫ ω, |Y ω| ^ 4 ∂μ) :
    (Real.rpow (∫ ω, |Y ω| ^ 2 ∂μ) ((3 : ℝ) / 2)) /
        Real.sqrt (∫ ω, |Y ω| ^ 4 ∂μ) ≤ ∫ ω, |Y ω| ∂μ := by sorry

end TightCoreset2027.Euclidean
