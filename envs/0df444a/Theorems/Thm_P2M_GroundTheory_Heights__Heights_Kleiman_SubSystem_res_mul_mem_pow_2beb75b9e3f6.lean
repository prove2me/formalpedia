-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_res_mul_mem_pow_2beb75b9e3f6
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_res_mul_mem_pow_2beb75b9e3f6
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:00:46.79792+00:00
-- url     : https://prove2.me/theorems/639560b7-f293-5624-8621-b3e5eb422d5c
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sub System res mul mem pow 2beb75b9e3f6: P2 M Ground Theory Heights  Heights Kleiman Sub System res mul mem pow 2beb75b9e3f6
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sub System res mul mem pow 2beb75b9e3f6 construction uses the P2 M Ground Theory Heights  Heights Kleiman Sub System res mul mem pow 2beb75b9e3f6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionPowers.lean#L28-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionPowers.lean#L28-L49

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionPowers
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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_res_mul_mem_pow_2beb75b9e3f6 (H : SubSystem S x Ω) (I : Chart x) {m : ℕ} {a : Ω}
    (ha : a ∈ (H.pow m).sub I) (n : ℕ) {b : Ω} (hb : b ∈ (H.pow n).sub I) :
    a * b ∈ (H.pow (m + n)).sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SubSystem».«res_mul_mem_pow» := P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_res_mul_mem_pow_2beb75b9e3f6
