-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjContract_isIntersectionTheory_47d65c2b728e
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ProjContract_isIntersectionTheory_47d65c2b728e
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:06:02.665146+00:00
-- url     : https://prove2.me/theorems/08fdfefc-f206-480d-ba82-b2e17fd066e2
-- title:
--   P2 M Ground Theory Heights  Heights Targets Proj Contract is Intersection Theory 47d65c2b728e: P2 M Ground Theory Heights  Heights Targets Proj Contract is Intersection Theory 47d65c2b728e
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Proj Contract is Intersection Theory 47d65c2b728e construction uses the P2 M Ground Theory Heights  Heights Targets Proj Contract is Intersection Theory 47d65c2b728e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ProjContract.lean#L42-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ProjContract.lean#L42-L61

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

theorem P2M_GroundTheory_Heights__Heights_Targets_ProjContract_isIntersectionTheory_47d65c2b728e (I : AI.I1.IFamily F ι) (hI : AI.I1.IsFieldIntersection I) :
    FieldNumbers.IsIntersectionTheory F I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ProjContract».«isIntersectionTheory» := P2M_GroundTheory_Heights__Heights_Targets_ProjContract_isIntersectionTheory_47d65c2b728e
