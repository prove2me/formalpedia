-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointDegreeComplexPositive_card_algHom_pos_89873825872a
-- name    : P2M_GroundTheory_Heights__Heights_PointDegreeComplexPositive_card_algHom_pos_89873825872a
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:15:32.60374+00:00
-- url     : https://prove2.me/theorems/4b1a56f4-b076-4ac4-86f6-86fecf0f1fc5
-- title:
--   P2 M Ground Theory Heights  Heights Point Degree Complex Positive card alg Hom pos 89873825872a: P2 M Ground Theory Heights  Heights Point Degree Complex Positive card alg Hom pos 89873825872a
-- statement:
--   The P2 M Ground Theory Heights  Heights Point Degree Complex Positive card alg Hom pos 89873825872a construction uses the P2 M Ground Theory Heights  Heights Point Degree Complex Positive card alg Hom pos 89873825872a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PPointDegCPos.lean#L14-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PPointDegCPos.lean#L14-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_IsArithVarBotDualBlocksUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PPointDegCPos
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.PointDegreeComplexPositive

theorem P2M_GroundTheory_Heights__Heights_PointDegreeComplexPositive_card_algHom_pos_89873825872a {K' : Type} [Field K'] [NumberField K'] (E : IntermediateField ℚ K') :
    0 < Nat.card (E →ₐ[ℚ] ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PointDegreeComplexPositive».«card_algHom_pos» := P2M_GroundTheory_Heights__Heights_PointDegreeComplexPositive_card_algHom_pos_89873825872a
