-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_pow_sub_af11ca77aee4
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_pow_sub_af11ca77aee4
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T06:32:31.05501+00:00
-- url     : https://prove2.me/theorems/4605ee01-4671-4eaf-9411-f968c8053652
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Step Three Away pow sub af11ca77aee4: P2 M Ground Theory Heights  Heights Kleiman Step Three Away pow sub af11ca77aee4
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Step Three Away pow sub af11ca77aee4 construction uses the P2 M Ground Theory Heights  Heights Kleiman Step Three Away pow sub af11ca77aee4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThreeAway.lean#L85-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThreeAway.lean#L85-L90

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_pow_sub_af11ca77aee4 (Q : SubSystem S x Ω) (I : Chart x) (n : ℕ) : (Q.pow n).sub I = Q.sub I ^ n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«StepThree».«Away».«pow_sub» := P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_pow_sub_af11ca77aee4
