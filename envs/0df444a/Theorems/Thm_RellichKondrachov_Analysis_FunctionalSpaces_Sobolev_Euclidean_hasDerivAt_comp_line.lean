-- Prove2me | Theorems.Thm_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_hasDerivAt_comp_line
-- name    : RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.hasDerivAt_comp_line
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:52:27.945192+00:00
-- url     : https://prove2.me/theorems/7cab1fe1-bc9e-4f3c-adc1-51c2fd49bd17
-- title:
--   Euclidean: has Deriv At comp line
-- statement:
--   The Euclidean construction uses the has Deriv At comp line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/rellich-kondrachov-lean4341.patch#L64-L71
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/rellich-kondrachov-lean4341.patch#L64-L71

import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_H1
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_TranslationEstimate
set_option autoImplicit true
open RellichKondrachov
open RellichKondrachov.Analysis
open RellichKondrachov.Analysis.FunctionalSpaces
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean
open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instMeasurableSpaceTranslationEstimate
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instBorelSpaceTranslationEstimate
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instOpensMeasurableSpaceTranslationEstimate

theorem RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.hasDerivAt_comp_line
    {f : E → ℝ} (hf : ContDiff ℝ 1 f) (x a : E) (t : ℝ) :
    HasDerivAt (fun t => f (line (x := x) (a := a) t))
      (fderiv ℝ f (line (x := x) (a := a) t) a) t := by sorry
