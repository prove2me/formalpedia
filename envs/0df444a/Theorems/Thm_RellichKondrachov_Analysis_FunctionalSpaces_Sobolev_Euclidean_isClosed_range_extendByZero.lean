-- Prove2me | Theorems.Thm_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_isClosed_range_extendByZero
-- name    : RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.isClosed_range_extendByZero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:53:17.631863+00:00
-- url     : https://prove2.me/theorems/b9d481cd-1a1e-4499-a538-37038578a6b7
-- title:
--   Euclidean: is Closed range extend By Zero
-- statement:
--   The Euclidean construction uses the is Closed range extend By Zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/rellich-kondrachov-lean4341.patch#L272-L289
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/rellich-kondrachov-lean4341.patch#L272-L289

import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_TranslationEstimateH1
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_FrechetKolmogorov
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Kernels
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_TranslationIntegral
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_Rellich
set_option autoImplicit true
open RellichKondrachov
open RellichKondrachov.Analysis
open RellichKondrachov.Analysis.FunctionalSpaces
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean
open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instMeasurableSpaceRellich
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instBorelSpaceRellich
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instOpensMeasurableSpaceRellich
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instMeasurableAddRellich
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instMeasurableNegRellich
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instFactOneLeTwoSobolevEuclideanRellich
omit [CompleteSpace E]

theorem RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.isClosed_range_extendByZero (K : Set E) (hKm : MeasurableSet K) :
    IsClosed
      (LinearMap.range
          ((MeasureTheory.Lp.extendByZeroₗᵢ
                (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K) hKm).toLinearMap) :
        Set (E →₂[(volume : Measure E)] ℝ)) := by sorry
