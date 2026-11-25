-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KThm_lbPow_toSubSystem_1a6630de4309
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KThm_lbPow_toSubSystem_1a6630de4309
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:57:05.284874+00:00
-- url     : https://prove2.me/theorems/fed77777-d8e5-527d-b85e-4ab4974bcf7b
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KThm lb Pow to Sub System 1a6630de4309: P2 M Ground Theory Heights  Heights Kleiman KThm lb Pow to Sub System 1a6630de4309
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KThm lb Pow to Sub System 1a6630de4309 construction uses the P2 M Ground Theory Heights  Heights Kleiman KThm lb Pow to Sub System 1a6630de4309 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleNefPlusAmple.lean#L184-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleNefPlusAmple.lean#L184-L190

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GeneratedTwistSysZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleNefPlusAmple
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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KThm_lbPow_toSubSystem_1a6630de4309 (Q : LineBundle S x) (n : ℕ) :
    (KThm.lbPow Q n).toSubSystem = Q.toSubSystem.pow n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KThm».«lbPow_toSubSystem» := P2M_GroundTheory_Heights__Heights_Kleiman_KThm_lbPow_toSubSystem_1a6630de4309
