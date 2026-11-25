-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_IdealTwistFamily_idealMod_fg_96ac575d611f
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_IdealTwistFamily_idealMod_fg_96ac575d611f
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:55:52.480958+00:00
-- url     : https://prove2.me/theorems/2f02b849-32c9-4032-b6ac-ded1bbed4e11
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Ideal Twist Family ideal Mod fg 96ac575d611f: P2 M Ground Theory Heights  Heights Kleiman Ideal Twist Family ideal Mod fg 96ac575d611f
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Ideal Twist Family ideal Mod fg 96ac575d611f construction uses the P2 M Ground Theory Heights  Heights Kleiman Ideal Twist Family ideal Mod fg 96ac575d611f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PIdealTwistFamily.lean#L149-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PIdealTwistFamily.lean#L149-L194

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsIdealTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PIdealTwistFamily
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
open GroundTheory.Heights₂.Heights.Kleiman.IdealTwistFamily
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_IdealTwistFamily_idealMod_fg_96ac575d611f [IsNoetherianRing S] (J' : Ideal (Poly S N))
    (hJ' : ∀ p ∈ J', ∀ d : ℕ, homogeneousComponent d p ∈ J') (I : Chart x) :
    (idealMod J' I).FG := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«IdealTwistFamily».«idealMod_fg» := P2M_GroundTheory_Heights__Heights_Kleiman_IdealTwistFamily_idealMod_fg_96ac575d611f
