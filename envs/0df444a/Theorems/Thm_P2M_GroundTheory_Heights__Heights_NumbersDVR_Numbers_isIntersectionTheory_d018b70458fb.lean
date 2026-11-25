-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_Numbers_isIntersectionTheory_d018b70458fb
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_Numbers_isIntersectionTheory_d018b70458fb
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:08:56.236281+00:00
-- url     : https://prove2.me/theorems/5b186636-3633-40b4-908c-8efd6486955c
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Numbers is Intersection Theory d018b70458fb: P2 M Ground Theory Heights  Heights Numbers DVR Numbers is Intersection Theory d018b70458fb
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Numbers is Intersection Theory d018b70458fb construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Numbers is Intersection Theory d018b70458fb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/IsFieldIntersectionExample.lean#L80-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/IsFieldIntersectionExample.lean#L80-L101

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumIsFieldIntersection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumRatSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVocabMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVocabMultiHomogIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVocabDivCycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumUnique
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsFieldIntersectionExample
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.NumbersDVR.Numbers
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_Numbers_isIntersectionTheory_d018b70458fb (hPt : IntNumPoint.Statement.{u})
    (hBase : FieldNumbers.IntNumBase.Statement.{u}) {I : IFamily F ι}
    (hI : IsFieldIntersection I) : FieldNumbers.IsIntersectionTheory F I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«Numbers».«isIntersectionTheory» := P2M_GroundTheory_Heights__Heights_NumbersDVR_Numbers_isIntersectionTheory_d018b70458fb
