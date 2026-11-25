-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mul_mem_of_mem_span_3875fb0ba4e8
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_mul_mem_of_mem_span_3875fb0ba4e8
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:09:46.524606+00:00
-- url     : https://prove2.me/theorems/d25f7b56-5ed4-5c06-8646-4f5325d3eb3c
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman mul mem of mem span 3875fb0ba4e8: P2 M Ground Theory Heights  Heights Kleiman mul mem of mem span 3875fb0ba4e8
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman mul mem of mem span 3875fb0ba4e8 construction uses the P2 M Ground Theory Heights  Heights Kleiman mul mem of mem span 3875fb0ba4e8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistSplitChart.lean#L55-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistSplitChart.lean#L55-L71

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistSplitObj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistSplitChart
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
open MvPolynomial Pointwise
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {r : ℕ} (η : Fin (r + 1) → Ω)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_mul_mem_of_mem_span_3875fb0ba4e8 {K : Chart x} (T : Submodule (chartRing S x K) Ω) {s t : Set Ω} (w : Ω)
    (h : ∀ u ∈ s, ∀ v ∈ t, w * (u * v) ∈ T) {u v : Ω} (hu : u ∈ Submodule.span (chartRing S x K) s)
    (hv : v ∈ Submodule.span (chartRing S x K) t) : w * (u * v) ∈ T := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«mul_mem_of_mem_span» := P2M_GroundTheory_Heights__Heights_Kleiman_mul_mem_of_mem_span_3875fb0ba4e8
