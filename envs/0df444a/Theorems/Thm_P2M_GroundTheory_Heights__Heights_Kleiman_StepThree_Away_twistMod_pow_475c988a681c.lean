-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_twistMod_pow_475c988a681c
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_twistMod_pow_475c988a681c
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:09:05.651841+00:00
-- url     : https://prove2.me/theorems/cb00d436-f5f2-49e0-b7d3-21fe2145d847
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Step Three Away twist Mod pow 475c988a681c: P2 M Ground Theory Heights  Heights Kleiman Step Three Away twist Mod pow 475c988a681c
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Step Three Away twist Mod pow 475c988a681c construction uses the P2 M Ground Theory Heights  Heights Kleiman Step Three Away twist Mod pow 475c988a681c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThreeAway.lean#L75-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThreeAway.lean#L75-L83

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_twistMod_pow_475c988a681c (a : ℤ) (I : Chart x) (n : ℕ) :
    twistMod S x a I ^ n = twistMod S x (n * a) I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«StepThree».«Away».«twistMod_pow» := P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_twistMod_pow_475c988a681c
