-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LineBundle_res_exists_mul_mem_pow_f29f9a78302a
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_LineBundle_res_exists_mul_mem_pow_f29f9a78302a
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:55:05.269843+00:00
-- url     : https://prove2.me/theorems/5e455317-391c-4155-ae82-57b75fa2ff9b
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Line Bundle res exists mul mem pow f29f9a78302a: P2 M Ground Theory Heights  Heights Kleiman Line Bundle res exists mul mem pow f29f9a78302a
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Line Bundle res exists mul mem pow f29f9a78302a construction uses the P2 M Ground Theory Heights  Heights Kleiman Line Bundle res exists mul mem pow f29f9a78302a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionPowers.lean#L51-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionPowers.lean#L51-L84

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_LineBundle_res_exists_mul_mem_pow_f29f9a78302a (H : LineBundle S x) {I J : Chart x} (hIJ : I.1 ⊆ J.1)
    (n : ℕ) {z : Ω} (hz : z ∈ (H.pow n).sub J) :
    ∃ a : chartRing S x I, IsUnit (chartIncl hIJ a) ∧ (a : Ω) * z ∈ (H.pow n).sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«LineBundle».«res_exists_mul_mem_pow» := P2M_GroundTheory_Heights__Heights_Kleiman_LineBundle_res_exists_mul_mem_pow_f29f9a78302a
