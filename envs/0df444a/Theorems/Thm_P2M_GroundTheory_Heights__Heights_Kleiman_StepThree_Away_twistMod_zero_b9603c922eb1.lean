-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_twistMod_zero_b9603c922eb1
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_twistMod_zero_b9603c922eb1
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T06:33:43.077736+00:00
-- url     : https://prove2.me/theorems/c15c958e-f005-5c2a-9e7b-c0402a68b553
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Step Three Away twist Mod zero b9603c922eb1: P2 M Ground Theory Heights  Heights Kleiman Step Three Away twist Mod zero b9603c922eb1
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Step Three Away twist Mod zero b9603c922eb1 construction uses the P2 M Ground Theory Heights  Heights Kleiman Step Three Away twist Mod zero b9603c922eb1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThreeAway.lean#L64-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThreeAway.lean#L64-L66

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_twistMod_zero_b9603c922eb1 (I : Chart x) : twistMod S x 0 I = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«StepThree».«Away».«twistMod_zero» := P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_twistMod_zero_b9603c922eb1
