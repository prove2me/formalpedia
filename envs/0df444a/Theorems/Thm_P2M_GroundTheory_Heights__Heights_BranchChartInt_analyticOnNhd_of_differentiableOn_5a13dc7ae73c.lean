-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BranchChartInt_analyticOnNhd_of_differentiableOn_5a13dc7ae73c
-- name    : P2M_GroundTheory_Heights__Heights_BranchChartInt_analyticOnNhd_of_differentiableOn_5a13dc7ae73c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:52.311791+00:00
-- url     : https://prove2.me/theorems/b346823a-c185-4f99-ad47-e46c157ebe0a
-- title:
--   P2 M Ground Theory Heights  Heights Branch Chart Int analytic On Nhd of differentiable On 5a13dc7ae73c: P2 M Ground Theory Heights  Heights Branch Chart Int analytic On Nhd of differentiable On 5a13dc
-- statement:
--   The P2 M Ground Theory Heights  Heights Branch Chart Int analytic On Nhd of differentiable On 5a13dc7ae73c construction uses the P2 M Ground Theory Heights  Heights Branch Chart Int analytic On Nhd of differentiable On 5a13dc7ae73c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PBranchChartInt.lean#L18-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PBranchChartInt.lean#L18-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchChartInt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolomorphicFibreSumInt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchSheetAE
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PBranchChartInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets ReciprocityTheory.AnForm.A
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.BranchChartInt

theorem P2M_GroundTheory_Heights__Heights_BranchChartInt_analyticOnNhd_of_differentiableOn_5a13dc7ae73c {k m : ℕ} {U : Set (Fin k → ℂ)} {f : (Fin k → ℂ) → Fin m → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) : AnalyticOnNhd ℂ f U := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BranchChartInt».«analyticOnNhd_of_differentiableOn» := P2M_GroundTheory_Heights__Heights_BranchChartInt_analyticOnNhd_of_differentiableOn_5a13dc7ae73c
