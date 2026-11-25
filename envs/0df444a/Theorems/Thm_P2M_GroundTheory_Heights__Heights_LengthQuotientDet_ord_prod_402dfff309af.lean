-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LengthQuotientDet_ord_prod_402dfff309af
-- name    : P2M_GroundTheory_Heights__Heights_LengthQuotientDet_ord_prod_402dfff309af
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:27:38.905858+00:00
-- url     : https://prove2.me/theorems/22a2cc64-8d1d-47e3-80ea-b099c8d2ec2f
-- title:
--   P2 M Ground Theory Heights  Heights Length Quotient Det ord prod 402dfff309af: P2 M Ground Theory Heights  Heights Length Quotient Det ord prod 402dfff309af
-- statement:
--   The P2 M Ground Theory Heights  Heights Length Quotient Det ord prod 402dfff309af construction uses the P2 M Ground Theory Heights  Heights Length Quotient Det ord prod 402dfff309af property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PLengthQuotientDet.lean#L9-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PLengthQuotientDet.lean#L9-L16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PLengthQuotientDet
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
open Module

theorem P2M_GroundTheory_Heights__Heights_LengthQuotientDet_ord_prod_402dfff309af {O : Type} [CommRing O] [IsDomain O] {ι : Type*} (s : Finset ι)
    (a : ι → O) (ha : ∀ i, a i ≠ 0) : Ring.ord O (∏ i ∈ s, a i) = ∑ i ∈ s, Ring.ord O (a i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LengthQuotientDet».«ord_prod» := P2M_GroundTheory_Heights__Heights_LengthQuotientDet_ord_prod_402dfff309af
