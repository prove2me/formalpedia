-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KThm_span_zpow_pow_d59270f20e61
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KThm_span_zpow_pow_d59270f20e61
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T06:39:58.91881+00:00
-- url     : https://prove2.me/theorems/a4c799b8-6801-4fcd-ae01-5265f4b61bb2
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KThm span zpow pow d59270f20e61: P2 M Ground Theory Heights  Heights Kleiman KThm span zpow pow d59270f20e61
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KThm span zpow pow d59270f20e61 construction uses the P2 M Ground Theory Heights  Heights Kleiman KThm span zpow pow d59270f20e61 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleNefPlusAmple.lean#L47-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleNefPlusAmple.lean#L47-L55

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KThm_span_zpow_pow_d59270f20e61 (I : Chart x) {i : Fin (N + 1)} (hi : i ∈ I.1) (a : ℤ) (n : ℕ) :
    Submodule.span (chartRing S x I) {x i ^ a} ^ n =
      Submodule.span (chartRing S x I) {x i ^ (a * n)} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KThm».«span_zpow_pow» := P2M_GroundTheory_Heights__Heights_Kleiman_KThm_span_zpow_pow_d59270f20e61
