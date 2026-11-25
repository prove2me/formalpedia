-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjContract_ratDiv_eq_3319c2ebbdca
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ProjContract_ratDiv_eq_3319c2ebbdca
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:07:24.020806+00:00
-- url     : https://prove2.me/theorems/ad2d6c06-c35d-5478-8f81-96493b94973d
-- title:
--   P2 M Ground Theory Heights  Heights Targets Proj Contract rat Div eq 3319c2ebbdca: P2 M Ground Theory Heights  Heights Targets Proj Contract rat Div eq 3319c2ebbdca
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Proj Contract rat Div eq 3319c2ebbdca construction uses the P2 M Ground Theory Heights  Heights Targets Proj Contract rat Div eq 3319c2ebbdca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ProjContract.lean#L36-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ProjContract.lean#L36-L40

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Assembly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_BlockInclInjectiveOfEmbedding
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ProjContract
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.Targets.ProjContract
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]
omit [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_Targets_ProjContract_ratDiv_eq_3319c2ebbdca (P : Ideal (NumbersDVR.MRing ι F)) (f g : NumbersDVR.MRing ι F)
    (W : Ideal (NumbersDVR.MRing ι F)) :
    NumbersDVR.ratDiv P f g W = AI.I1.ratDiv P f g W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ProjContract».«ratDiv_eq» := P2M_GroundTheory_Heights__Heights_Targets_ProjContract_ratDiv_eq_3319c2ebbdca
