-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightLowerBound_of_leaves_e4aa9edac6ec
-- name    : P2M_GroundTheory_Heights__Heights_ChowHeightLowerBound_of_leaves_e4aa9edac6ec
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:10:20.256385+00:00
-- url     : https://prove2.me/theorems/4095251e-7efb-448b-bba8-6804b81e272c
-- title:
--   P2 M Ground Theory Heights  Heights Chow Height Lower Bound of leaves e4aa9edac6ec: P2 M Ground Theory Heights  Heights Chow Height Lower Bound of leaves e4aa9edac6ec
-- statement:
--   The P2 M Ground Theory Heights  Heights Chow Height Lower Bound of leaves e4aa9edac6ec construction uses the P2 M Ground Theory Heights  Heights Chow Height Lower Bound of leaves e4aa9edac6ec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/OfLeaves.lean#L46-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/OfLeaves.lean#L46-L53

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_RenameProdMapMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_HeightMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LineInhabitant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLogBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PBaseChangeLogBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PRecursion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PCharacterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_OfLeaves
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

theorem P2M_GroundTheory_Heights__Heights_ChowHeightLowerBound_of_leaves_e4aa9edac6ec (hV : ChowFormSectionVertical.Statement)
    (hA : MahlerSection.Statement) (hS : ChowFormSection.Statement)
    (hB : ChowFormBaseChange.Statement) (hAv : BaseChangeAvoid.Statement)
    (hMass : ConeIntegralMass.Statement) (hFin : ConeBallFinite.Statement)
    (hInt : ConeFsLogIntegrable.Statement) (hNull : ConeHyperplaneNull.Statement) :
    ChowHeightLowerBound.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChowHeightLowerBound».«of_leaves» := P2M_GroundTheory_Heights__Heights_ChowHeightLowerBound_of_leaves_e4aa9edac6ec
