-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_IdealTwistFamily_exists_unit_mul_mem_of_span_3d253f35998c
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_IdealTwistFamily_exists_unit_mul_mem_of_span_3d253f35998c
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T06:16:56.115978+00:00
-- url     : https://prove2.me/theorems/5bb55cd3-a91e-4bdc-8f6b-731a4d790f1a
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Ideal Twist Family exists unit mul mem of span 3d253f35998c: P2 M Ground Theory Heights  Heights Kleiman Ideal Twist Family exists unit mul mem of span 3d25
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Ideal Twist Family exists unit mul mem of span 3d253f35998c construction uses the P2 M Ground Theory Heights  Heights Kleiman Ideal Twist Family exists unit mul mem of span 3d253f35998c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PIdealTwistFamily.lean#L100-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PIdealTwistFamily.lean#L100-L124

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsIdealTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PIdealTwistFamily
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
open GroundTheory.Heights₂.Heights.Kleiman.IdealTwistFamily
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_IdealTwistFamily_exists_unit_mul_mem_of_span_3d253f35998c {I J : Chart x} (h : I.1 ⊆ J.1)
    (M : Submodule (chartRing S x I) Ω) {G : Set Ω}
    (hG : ∀ g ∈ G, ∃ a : chartRing S x I, IsUnit (chartIncl h a) ∧ (a : Ω) * g ∈ M)
    {y : Ω} (hy : y ∈ Submodule.span (chartRing S x J) G) :
    ∃ a : chartRing S x I, IsUnit (chartIncl h a) ∧ (a : Ω) * y ∈ M := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«IdealTwistFamily».«exists_unit_mul_mem_of_span» := P2M_GroundTheory_Heights__Heights_Kleiman_IdealTwistFamily_exists_unit_mul_mem_of_span_3d253f35998c
