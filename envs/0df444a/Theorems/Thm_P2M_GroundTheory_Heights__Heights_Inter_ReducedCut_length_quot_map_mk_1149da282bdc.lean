-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ReducedCut_length_quot_map_mk_1149da282bdc
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ReducedCut_length_quot_map_mk_1149da282bdc
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:42:46.745799+00:00
-- url     : https://prove2.me/theorems/e0db9d14-4733-4b64-8004-00d176f015c5
-- title:
--   P2 M Ground Theory Heights  Heights Inter Reduced Cut length quot map mk 1149da282bdc: P2 M Ground Theory Heights  Heights Inter Reduced Cut length quot map mk 1149da282bdc
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Reduced Cut length quot map mk 1149da282bdc construction uses the P2 M Ground Theory Heights  Heights Inter Reduced Cut length quot map mk 1149da282bdc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PReducedCutLength.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PReducedCutLength.lean#L15-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsReducedCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_OrdModEqLengthQuotSup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LengthLocalizedModuleQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LocalMultRadical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PReducedCutLength
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open GroundTheory.Heights₂.Heights.Inter.ReducedCut
open IsLocalRing

theorem P2M_GroundTheory_Heights__Heights_Inter_ReducedCut_length_quot_map_mk_1149da282bdc {L : Type*} [CommRing L] (J₀ J : Ideal L) :
    Module.length (L ⧸ J₀) ((L ⧸ J₀) ⧸ J.map (Ideal.Quotient.mk J₀)) =
      Module.length L (L ⧸ (J₀ ⊔ J)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ReducedCut».«length_quot_map_mk» := P2M_GroundTheory_Heights__Heights_Inter_ReducedCut_length_quot_map_mk_1149da282bdc
