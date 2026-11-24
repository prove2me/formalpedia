-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_card_quot_span_eq_relIndex_7d79e126b957
-- name    : P2M_GroundTheory_Heights__Heights_card_quot_span_eq_relIndex_7d79e126b957
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:54.562048+00:00
-- url     : https://prove2.me/theorems/4e8404ac-4d4a-47fd-97c9-8fedbcd4aa59
-- title:
--   P2 M Ground Theory Heights  Heights card quot span eq rel Index 7d79e126b957: P2 M Ground Theory Heights  Heights card quot span eq rel Index 7d79e126b957
-- statement:
--   The P2 M Ground Theory Heights  Heights card quot span eq rel Index 7d79e126b957 construction uses the P2 M Ground Theory Heights  Heights card quot span eq rel Index 7d79e126b957 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/PLocalQuotCentred.lean#L11-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/PLocalQuotCentred.lean#L11-L24

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

theorem P2M_GroundTheory_Heights__Heights_card_quot_span_eq_relIndex_7d79e126b957 {L : Type*} [CommRing L] (R : Subring L) (x : R) :
    Nat.card (R ⧸ Ideal.span {x}) =
      (R.toAddSubgroup.map (AddMonoidHom.mulLeft (x : L))).relIndex R.toAddSubgroup := by sorry

alias «GroundTheory».«Heights₂».«Heights».«card_quot_span_eq_relIndex» := P2M_GroundTheory_Heights__Heights_card_quot_span_eq_relIndex_7d79e126b957
