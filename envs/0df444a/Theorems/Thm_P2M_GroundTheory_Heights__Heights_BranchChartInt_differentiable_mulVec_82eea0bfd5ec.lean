-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BranchChartInt_differentiable_mulVec_82eea0bfd5ec
-- name    : P2M_GroundTheory_Heights__Heights_BranchChartInt_differentiable_mulVec_82eea0bfd5ec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:05.95377+00:00
-- url     : https://prove2.me/theorems/548daafb-5bde-42e4-8ac1-6bb8e75e963e
-- title:
--   P2 M Ground Theory Heights  Heights Branch Chart Int differentiable mul Vec 82eea0bfd5ec: P2 M Ground Theory Heights  Heights Branch Chart Int differentiable mul Vec 82eea0bfd5ec
-- statement:
--   The P2 M Ground Theory Heights  Heights Branch Chart Int differentiable mul Vec 82eea0bfd5ec construction uses the P2 M Ground Theory Heights  Heights Branch Chart Int differentiable mul Vec 82eea0bfd5ec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PBranchChartInt.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PBranchChartInt.lean#L28-L30

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

theorem P2M_GroundTheory_Heights__Heights_BranchChartInt_differentiable_mulVec_82eea0bfd5ec {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℂ) :
    Differentiable ℂ (fun x : Fin n → ℂ => A *ᵥ x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BranchChartInt».«differentiable_mulVec» := P2M_GroundTheory_Heights__Heights_BranchChartInt_differentiable_mulVec_82eea0bfd5ec
