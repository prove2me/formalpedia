-- Prove2me | Theorems.Thm_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_isCompactOperator_h1OnToL2_codRestrict_range_extendByZero
-- name    : RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.isCompactOperator_h1OnToL2_codRestrict_range_extendByZero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:38:40.367264+00:00
-- url     : https://prove2.me/theorems/dcf8f0cb-89a3-4b69-af2e-63f5740bcc66
-- title:
--   Euclidean: is Compact Operator h1 On To L2 cod Restrict range extend By Zero
-- statement:
--   The Euclidean construction uses the is Compact Operator h1 On To L2 cod Restrict range extend By Zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/rellich-kondrachov-lean4341.patch#L291-L341
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/rellich-kondrachov-lean4341.patch#L291-L341

import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_TranslationEstimateH1
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_FrechetKolmogorov
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Kernels
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_TranslationIntegral
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_Rellich
import Theorems.Thm_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_smoothBCF_apply
attribute [local simp] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.smoothBCF_apply


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

theorem RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.isCompactOperator_h1OnToL2_codRestrict_range_extendByZero {K : Set E} (hK : IsCompact K)
    (hKm : MeasurableSet K) :
    IsCompactOperator
      (Set.codRestrict
        (h1OnToL2 (E := E) K hKm)
        (LinearMap.range
          ((MeasureTheory.Lp.extendByZeroₗᵢ
                (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K) hKm).toLinearMap))
        (by
          intro x
          have hxmem : (x : ↥(h1 (μ := (volume : Measure E)) (E := E))) ∈ h1On (E := E) K hKm :=
            x.property
          dsimp [h1On] at hxmem
          -- Rewrite the codomain-restricted inclusion as `h1ToL2` on the underlying `H¹` element.
          change
              ((h1ToL2 (μ := (volume : Measure E)) (E := E)).toLinearMap
                    (x : ↥(h1 (μ := (volume : Measure E)) (E := E)))) ∈
                LinearMap.range
                  ((MeasureTheory.Lp.extendByZeroₗᵢ
                        (μ := (volume : Measure E)) (E := ℝ)
                        (p := (2 : ℝ≥0∞))
                        (s := K) hKm).toLinearMap)
          -- This is exactly the unfolded membership in
          -- the `comap`.
          exact hxmem)) := by sorry
