-- Prove2me | Theorems.Thm_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_enorm_translateL2_sub_toL2_le
-- name    : RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.enorm_translateL2_sub_toL2_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:52:23.737554+00:00
-- url     : https://prove2.me/theorems/fb52715e-3985-4580-ab71-96f2f11bf220
-- title:
--   Euclidean: enorm translate L2 sub to L2 le
-- statement:
--   The Euclidean construction uses the enorm translate L2 sub to L2 le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/rellich-kondrachov-lean4341.patch#L235-L344
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/rellich-kondrachov-lean4341.patch#L235-L344

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

theorem RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.enorm_translateL2_sub_toL2_le (a : E) (f : ↥(C1c (E := E))) :
    ‖translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) -
        toL2 (μ := μ) (E := E) f‖ₑ ≤
      ‖a‖ₑ * ‖toL2Grad (μ := μ) (E := E) f‖ₑ := by sorry
