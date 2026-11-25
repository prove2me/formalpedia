-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KThm_generated_twistSys_nat_4a88fe4e3490
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KThm_generated_twistSys_nat_4a88fe4e3490
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:56:53.538301+00:00
-- url     : https://prove2.me/theorems/c438c301-e5af-5a58-817d-37ac2003a468
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KThm generated twist Sys nat 4a88fe4e3490: P2 M Ground Theory Heights  Heights Kleiman KThm generated twist Sys nat 4a88fe4e3490
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KThm generated twist Sys nat 4a88fe4e3490 construction uses the P2 M Ground Theory Heights  Heights Kleiman KThm generated twist Sys nat 4a88fe4e3490 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleNefPlusAmple.lean#L101-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleNefPlusAmple.lean#L101-L109

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KThm_generated_twistSys_nat_4a88fe4e3490 (e : ℕ) : (twistSys S x e).Generated := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KThm».«generated_twistSys_nat» := P2M_GroundTheory_Heights__Heights_Kleiman_KThm_generated_twistSys_nat_4a88fe4e3490
