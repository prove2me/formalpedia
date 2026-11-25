-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_generated_twistSys_zero__031813fa5837
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_generated_twistSys_zero__031813fa5837
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:00:53.087062+00:00
-- url     : https://prove2.me/theorems/b157be6a-3b25-4ad4-ac87-5470492a82c1
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman generated twist Sys zero  031813fa5837: P2 M Ground Theory Heights  Heights Kleiman generated twist Sys zero  031813fa5837
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman generated twist Sys zero  031813fa5837 construction uses the P2 M Ground Theory Heights  Heights Kleiman generated twist Sys zero  031813fa5837 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/GeneratedTwistSysZero.lean#L26-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/GeneratedTwistSysZero.lean#L26-L40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GeneratedTwistSysZero
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
variable (k : Type u) [Field k]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_generated_twistSys_zero__031813fa5837 {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
    {x : Fin (N + 1) → Ω} : (twistSys S x 0).Generated := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«generated_twistSys_zero'» := P2M_GroundTheory_Heights__Heights_Kleiman_generated_twistSys_zero__031813fa5837
