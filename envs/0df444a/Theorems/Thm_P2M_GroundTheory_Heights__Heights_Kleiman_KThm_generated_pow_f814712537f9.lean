-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KThm_generated_pow_f814712537f9
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KThm_generated_pow_f814712537f9
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T06:40:28.560986+00:00
-- url     : https://prove2.me/theorems/89388f08-70ee-5bb1-bb29-0aeb28441d8d
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KThm generated pow f814712537f9: P2 M Ground Theory Heights  Heights Kleiman KThm generated pow f814712537f9
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KThm generated pow f814712537f9 construction uses the P2 M Ground Theory Heights  Heights Kleiman KThm generated pow f814712537f9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleNefPlusAmple.lean#L90-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleNefPlusAmple.lean#L90-L93

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KThm_generated_pow_f814712537f9 {Q : SubSystem S x Ω} (hQ : Q.Generated) (n : ℕ) : (Q.pow n).Generated := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KThm».«generated_pow» := P2M_GroundTheory_Heights__Heights_Kleiman_KThm_generated_pow_f814712537f9
