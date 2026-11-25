-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_IdealTwistFamily_idealMod_loc_beabb2cef896
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_IdealTwistFamily_idealMod_loc_beabb2cef896
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:55:53.812455+00:00
-- url     : https://prove2.me/theorems/8dc4334f-7039-4f11-8da1-7f0bb0e66448
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Ideal Twist Family ideal Mod loc beabb2cef896: P2 M Ground Theory Heights  Heights Kleiman Ideal Twist Family ideal Mod loc beabb2cef896
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Ideal Twist Family ideal Mod loc beabb2cef896 construction uses the P2 M Ground Theory Heights  Heights Kleiman Ideal Twist Family ideal Mod loc beabb2cef896 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PIdealTwistFamily.lean#L126-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PIdealTwistFamily.lean#L126-L147

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_IdealTwistFamily_idealMod_loc_beabb2cef896 {I J : Chart x} (h : I.1 ⊆ J.1) (J' : Ideal (Poly S N)) {y : Ω}
    (hy : y ∈ idealMod J' J) :
    ∃ a : chartRing S x I, IsUnit (chartIncl h a) ∧ (a : Ω) * y ∈ idealMod J' I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«IdealTwistFamily».«idealMod_loc» := P2M_GroundTheory_Heights__Heights_Kleiman_IdealTwistFamily_idealMod_loc_beabb2cef896
