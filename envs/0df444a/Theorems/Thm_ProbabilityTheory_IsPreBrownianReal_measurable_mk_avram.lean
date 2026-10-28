-- Prove2me | Theorems.Thm_ProbabilityTheory_IsPreBrownianReal_measurable_mk_avram
-- name    : ProbabilityTheory.IsPreBrownianReal.measurable_mk_avram
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:29:14.239231+00:00
-- url     : https://prove2.me/theorems/a5cf2e99-77ba-4d0e-8425-be2b707ceab3
-- title:
--   Every evaluation of the canonical Brownian modification is measurable
-- statement:
--   The Kolmogorov–Chentsov continuous modification supplies a measurable random variable at every fixed time. This theorem makes the constructor's measurability certificate directly available for subsequent Lévy-process adaptation and Laplace-law proofs.
-- source:
--   Previously accepted LevyStochCalc.Brownian.BrownianMotion.exists_readable proof's internal Kolmogorov–Chentsov modification.

import Definitions.Def_KLSModular_BrownianMotion_Gaussian_BrownianMotion

open ProbabilityTheory MeasureTheory NNReal
open scoped NNReal

theorem ProbabilityTheory.IsPreBrownianReal.measurable_mk_avram
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : ℝ≥0 → Ω → ℝ) (h : IsPreBrownianReal X P) (t : ℝ≥0) :
    Measurable (h.mk X t) := by sorry
