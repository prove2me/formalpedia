-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_res_mem_span_iff_exists_isUnit_1ef95d12e374
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_res_mem_span_iff_exists_isUnit_1ef95d12e374
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:03:58.263056+00:00
-- url     : https://prove2.me/theorems/93f28a0f-78c4-53a9-a44c-90d868ad679a
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman res mem span iff exists is Unit 1ef95d12e374: P2 M Ground Theory Heights  Heights Kleiman res mem span iff exists is Unit 1ef95d12e374
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman res mem span iff exists is Unit 1ef95d12e374 construction uses the P2 M Ground Theory Heights  Heights Kleiman res mem span iff exists is Unit 1ef95d12e374 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionPowers.lean#L251-L285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionPowers.lean#L251-L285

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_res_mem_span_iff_exists_isUnit_1ef95d12e374 {R : Set Ω} {I J : Chart x} (hIJ : I.1 ⊆ J.1) (z : Ω) :
    z ∈ Submodule.span (chartRing S x J) R ↔ ∃ a : chartRing S x I, IsUnit (chartIncl hIJ a) ∧
      (a : Ω) • z ∈ Submodule.span (chartRing S x I) R := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«res_mem_span_iff_exists_isUnit» := P2M_GroundTheory_Heights__Heights_Kleiman_res_mem_span_iff_exists_isUnit_1ef95d12e374
