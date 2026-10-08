-- Prove2me | Theorems.Thm_ParameterizedCalculus_smooth_unit_interval_integral
-- name    : ParameterizedCalculus.smooth_unit_interval_integral
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-06T18:40:07.793557+00:00
-- url     : https://prove2.me/theorems/6e87f73d-207c-4d95-ac4a-751124157675
-- title:
--   Smooth parameter dependence of a fixed-interval integral
-- statement:
--   Let $P$ be any real normed vector space, and let $h:P\times\mathbb R\to\mathbb R$ be jointly smooth. Then the function
--
--   $$H(p)=\int_0^1 h(p,s)\,ds$$
--
--   is smooth on $P$. No finite-dimensionality or completeness assumption on the parameter space is required. This supplies smooth dependence on parameters for the primitive and positive integrating factor used in scalar transport.
-- source:
--   Geiges, Contact geometry, https://arxiv.org/abs/math/0307242, proof of Theorem 2.20, printed pp. 14–15: analytic smooth-parameter integration underlying the conformal factor. Directly derived from Mathlib.MeasureTheory.contDiffOn_convolution_right_with_param_comp, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean (fixed-interval integration specialization with a smooth cutoff).

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open scoped ContDiff
open MeasureTheory

theorem ParameterizedCalculus.smooth_unit_interval_integral
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (h : P → ℝ → ℝ) (hh : ContDiff ℝ ∞ (Function.uncurry h)) :
    ContDiff ℝ ∞ (fun p => ∫ s in (0 : ℝ)..1, h p s) := by sorry
