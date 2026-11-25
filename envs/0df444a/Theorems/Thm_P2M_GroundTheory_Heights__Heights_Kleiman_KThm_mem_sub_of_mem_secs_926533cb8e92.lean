-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KThm_mem_sub_of_mem_secs_926533cb8e92
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KThm_mem_sub_of_mem_secs_926533cb8e92
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:58:05.596789+00:00
-- url     : https://prove2.me/theorems/cf3197e1-5791-5cc6-95fa-e8e3e1a8c869
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KThm mem sub of mem secs 926533cb8e92: P2 M Ground Theory Heights  Heights Kleiman KThm mem sub of mem secs 926533cb8e92
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KThm mem sub of mem secs 926533cb8e92 construction uses the P2 M Ground Theory Heights  Heights Kleiman KThm mem sub of mem secs 926533cb8e92 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleNefPlusAmple.lean#L64-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleNefPlusAmple.lean#L64-L67

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KThm_mem_sub_of_mem_secs_926533cb8e92 {F : SubSystem S x Ω} {z : Ω} (hz : z ∈ F.secs) (I : Chart x) :
    z ∈ F.sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KThm».«mem_sub_of_mem_secs» := P2M_GroundTheory_Heights__Heights_Kleiman_KThm_mem_sub_of_mem_secs_926533cb8e92
