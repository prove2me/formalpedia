-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KThm_span_zpow_mul_367f4f97d00d
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KThm_span_zpow_mul_367f4f97d00d
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T06:40:29.45526+00:00
-- url     : https://prove2.me/theorems/c74f5f87-39ba-4498-b8e9-188ed5540cc1
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KThm span zpow mul 367f4f97d00d: P2 M Ground Theory Heights  Heights Kleiman KThm span zpow mul 367f4f97d00d
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KThm span zpow mul 367f4f97d00d construction uses the P2 M Ground Theory Heights  Heights Kleiman KThm span zpow mul 367f4f97d00d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleNefPlusAmple.lean#L41-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleNefPlusAmple.lean#L41-L45

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KThm_span_zpow_mul_367f4f97d00d (I : Chart x) {i : Fin (N + 1)} (hi : i ∈ I.1) (a b : ℤ) :
    Submodule.span (chartRing S x I) {x i ^ a} * Submodule.span (chartRing S x I) {x i ^ b} =
      Submodule.span (chartRing S x I) {x i ^ (a + b)} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KThm».«span_zpow_mul» := P2M_GroundTheory_Heights__Heights_Kleiman_KThm_span_zpow_mul_367f4f97d00d
