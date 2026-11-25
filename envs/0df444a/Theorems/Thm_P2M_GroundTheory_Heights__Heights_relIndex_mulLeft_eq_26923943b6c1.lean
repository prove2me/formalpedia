-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_relIndex_mulLeft_eq_26923943b6c1
-- name    : P2M_GroundTheory_Heights__Heights_relIndex_mulLeft_eq_26923943b6c1
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:50:23.681547+00:00
-- url     : https://prove2.me/theorems/badb43f4-3afe-4188-87db-a0dba46cf010
-- title:
--   P2 M Ground Theory Heights  Heights rel Index mul Left eq 26923943b6c1: P2 M Ground Theory Heights  Heights rel Index mul Left eq 26923943b6c1
-- statement:
--   The P2 M Ground Theory Heights  Heights rel Index mul Left eq 26923943b6c1 construction uses the P2 M Ground Theory Heights  Heights rel Index mul Left eq 26923943b6c1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/PLocalQuotCentred.lean#L26-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/PLocalQuotCentred.lean#L26-L42

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightLocalQuotCentred
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightCentredRingNormal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightLocalNormalIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PLocalQuotCentred
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
open NumberField

theorem P2M_GroundTheory_Heights__Heights_relIndex_mulLeft_eq_26923943b6c1 {L : Type*} [CommRing L] [IsDomain L] (A B : Subring L) (hAB : A ≤ B)
    (hfin : A.toAddSubgroup.relIndex B.toAddSubgroup ≠ 0) (f : L) (hf : f ≠ 0) (hfA : f ∈ A) :
    (A.toAddSubgroup.map (AddMonoidHom.mulLeft f)).relIndex A.toAddSubgroup =
      (B.toAddSubgroup.map (AddMonoidHom.mulLeft f)).relIndex B.toAddSubgroup := by sorry

alias «GroundTheory».«Heights₂».«Heights».«relIndex_mulLeft_eq» := P2M_GroundTheory_Heights__Heights_relIndex_mulLeft_eq_26923943b6c1
