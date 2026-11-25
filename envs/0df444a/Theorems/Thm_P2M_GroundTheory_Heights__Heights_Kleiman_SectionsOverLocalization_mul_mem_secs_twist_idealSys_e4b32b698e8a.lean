-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_mul_mem_secs_twist_idealSys_e4b32b698e8a
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_mul_mem_secs_twist_idealSys_e4b32b698e8a
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:57:42.71583+00:00
-- url     : https://prove2.me/theorems/59c823c1-1205-41f0-a9c6-30c9be8b0e9b
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization mul mem secs twist ideal Sys e4b32b698e8a: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization mul mem secs tw
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization mul mem secs twist ideal Sys e4b32b698e8a construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization mul mem secs twist ideal Sys e4b32b698e8a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/MulMemSecsTwistIdealSys.lean#L15-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/MulMemSecsTwistIdealSys.lean#L15-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_BaseChangeTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_MulMemSecsTwistIdealSys
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
open MvPolynomial Kleiman
noncomputable section
variable {R : Type*} [CommRing R] {Ω : Type*} [Field Ω] [Algebra R Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_mul_mem_secs_twist_idealSys_e4b32b698e8a (J : Ideal (Poly R N)) {a : R} (ha : C a ∈ J)
    (F : SubSystem R x Ω) {y : Ω} (hy : y ∈ F.secs) :
    algebraMap R Ω a * y ∈ (F.twist (idealSys x J)).secs := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«mul_mem_secs_twist_idealSys» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_mul_mem_secs_twist_idealSys_e4b32b698e8a
