-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_zero_mem_ampleChart_441138514924
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_zero_mem_ampleChart_441138514924
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:23:06.026802+00:00
-- url     : https://prove2.me/theorems/ba53c6aa-7702-55a7-97c5-f75157b2a38b
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman zero mem ample Chart 441138514924: P2 M Ground Theory Heights  Heights Kleiman zero mem ample Chart 441138514924
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman zero mem ample Chart 441138514924 construction uses the P2 M Ground Theory Heights  Heights Kleiman zero mem ample Chart 441138514924 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestriction.lean#L13-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestriction.lean#L13-L16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionBundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestriction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w

theorem P2M_GroundTheory_Heights__Heights_Kleiman_zero_mem_ampleChart_441138514924 {S : Type u} [CommRing S] {E : Type w} [Field E] [Algebra S E] {M : ℕ}
    {z : Fin (M + 1) → E} {H : SubSystem S z E} {σ : E} {I : Chart z} :
    (0 : E) ∈ ampleChart H 1 σ I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«zero_mem_ampleChart» := P2M_GroundTheory_Heights__Heights_Kleiman_zero_mem_ampleChart_441138514924
