-- Prove2me | Theorems.Thm_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_norm_translateL2_sub_toL2_le
-- name    : RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.norm_translateL2_sub_toL2_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:52:34.957147+00:00
-- url     : https://prove2.me/theorems/5d2c2fbd-d92c-4efe-84c6-ff82ae7f22ca
-- title:
--   Euclidean: norm translate L2 sub to L2 le
-- statement:
--   Real-norm form of `enorm_translateL2_sub_toL2_le`.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/rellich-kondrachov-lean4341.patch#L347-L367
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/rellich-kondrachov-lean4341.patch#L347-L367

import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_Translation
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_TranslationEstimate
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_TranslationEstimateL2
set_option autoImplicit true
open RellichKondrachov
open RellichKondrachov.Analysis
open RellichKondrachov.Analysis.FunctionalSpaces
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean
open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instMeasurableSpaceTranslationEstimateL2
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instBorelSpaceTranslationEstimateL2
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instOpensMeasurableSpaceTranslationEstimateL2
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instMeasurableAddTranslationEstimateL2
attribute [local instance] instMeasurableSpaceTranslationEstimateL2 instBorelSpaceTranslationEstimateL2 instOpensMeasurableSpaceTranslationEstimateL2 instMeasurableAddTranslationEstimateL2
variable (μ : Measure E) [μ.IsAddRightInvariant] [IsFiniteMeasureOnCompacts μ] [SFinite μ]

theorem RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.norm_translateL2_sub_toL2_le (a : E) (f : ↥(C1c (E := E))) :
    ‖translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) -
        toL2 (μ := μ) (E := E) f‖ ≤
      ‖a‖ * ‖toL2Grad (μ := μ) (E := E) f‖ := by sorry
