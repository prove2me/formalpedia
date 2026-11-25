-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_twist_sub_46528efab20e
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_twist_sub_46528efab20e
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:33:12.710831+00:00
-- url     : https://prove2.me/theorems/f31f6a3a-9a70-57df-9979-e88ddb485f2f
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Step Three Away twist sub 46528efab20e: P2 M Ground Theory Heights  Heights Kleiman Step Three Away twist sub 46528efab20e
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Step Three Away twist sub 46528efab20e construction uses the P2 M Ground Theory Heights  Heights Kleiman Step Three Away twist sub 46528efab20e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThreeAway.lean#L53-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThreeAway.lean#L53-L62

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepThreeAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThreeAway
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
open GroundTheory.Heights₂.Heights.Kleiman.StepThree GroundTheory.Heights₂.Heights.Kleiman.StepThree.Away
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_twist_sub_46528efab20e (F Q : SubSystem S x Ω) (I : Chart x) :
    (F.twist Q).sub I = Q.sub I * F.sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«StepThree».«Away».«twist_sub» := P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_twist_sub_46528efab20e
