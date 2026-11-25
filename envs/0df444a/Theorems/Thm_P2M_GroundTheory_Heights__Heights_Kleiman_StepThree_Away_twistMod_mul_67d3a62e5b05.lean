-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_twistMod_mul_67d3a62e5b05
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_twistMod_mul_67d3a62e5b05
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T06:33:39.875524+00:00
-- url     : https://prove2.me/theorems/32c42fd6-bd54-4cb8-a84c-c93dc2296120
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Step Three Away twist Mod mul 67d3a62e5b05: P2 M Ground Theory Heights  Heights Kleiman Step Three Away twist Mod mul 67d3a62e5b05
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Step Three Away twist Mod mul 67d3a62e5b05 construction uses the P2 M Ground Theory Heights  Heights Kleiman Step Three Away twist Mod mul 67d3a62e5b05 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThreeAway.lean#L68-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThreeAway.lean#L68-L73

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_twistMod_mul_67d3a62e5b05 (a a' : ℤ) (I : Chart x) :
    twistMod S x a I * twistMod S x a' I = twistMod S x (a + a') I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«StepThree».«Away».«twistMod_mul» := P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_twistMod_mul_67d3a62e5b05
