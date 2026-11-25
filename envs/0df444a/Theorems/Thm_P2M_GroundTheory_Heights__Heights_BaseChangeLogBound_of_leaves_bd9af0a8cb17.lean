-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BaseChangeLogBound_of_leaves_bd9af0a8cb17
-- name    : P2M_GroundTheory_Heights__Heights_BaseChangeLogBound_of_leaves_bd9af0a8cb17
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:15:01.536775+00:00
-- url     : https://prove2.me/theorems/b5c66a97-d3a7-4e41-a744-cd582710bd5d
-- title:
--   P2 M Ground Theory Heights  Heights Base Change Log Bound of leaves bd9af0a8cb17: P2 M Ground Theory Heights  Heights Base Change Log Bound of leaves bd9af0a8cb17
-- statement:
--   The P2 M Ground Theory Heights  Heights Base Change Log Bound of leaves bd9af0a8cb17 construction uses the P2 M Ground Theory Heights  Heights Base Change Log Bound of leaves bd9af0a8cb17 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/OfLeaves.lean#L35-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/OfLeaves.lean#L35-L39

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

theorem P2M_GroundTheory_Heights__Heights_BaseChangeLogBound_of_leaves_bd9af0a8cb17 (hB : ChowFormBaseChange.Statement)
    (hAv : BaseChangeAvoid.Statement) (hMass : ConeIntegralMass.Statement)
    (hFin : ConeBallFinite.Statement) (hInt : ConeFsLogIntegrable.Statement)
    (hNull : ConeHyperplaneNull.Statement) : BaseChangeLogBound.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BaseChangeLogBound».«of_leaves» := P2M_GroundTheory_Heights__Heights_BaseChangeLogBound_of_leaves_bd9af0a8cb17
