-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KThm_mul_mem_secs_d5573022378d
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KThm_mul_mem_secs_d5573022378d
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:56:58.961281+00:00
-- url     : https://prove2.me/theorems/ee3ad997-fff4-5d1b-8578-f8c4b3d32948
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KThm mul mem secs d5573022378d: P2 M Ground Theory Heights  Heights Kleiman KThm mul mem secs d5573022378d
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KThm mul mem secs d5573022378d construction uses the P2 M Ground Theory Heights  Heights Kleiman KThm mul mem secs d5573022378d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleNefPlusAmple.lean#L75-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleNefPlusAmple.lean#L75-L80

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KThm_mul_mem_secs_d5573022378d {F Q : SubSystem S x Ω} {a b : Ω} (ha : a ∈ F.secs) (hb : b ∈ Q.secs) :
    b * a ∈ (F.twist Q).secs := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KThm».«mul_mem_secs» := P2M_GroundTheory_Heights__Heights_Kleiman_KThm_mul_mem_secs_d5573022378d
