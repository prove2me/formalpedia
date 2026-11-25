-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZChartSpan_exists_coeff_of_mem_twist_939e653bd620
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZChartSpan_exists_coeff_of_mem_twist_939e653bd620
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:59:58.201681+00:00
-- url     : https://prove2.me/theorems/d78c2407-e48b-5640-a9b8-f9c2992e9812
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Very Ample ZChart Span exists coeff of mem twist 939e653bd620: P2 M Ground Theory Heights  Heights Kleiman Very Ample ZChart Span exists coeff of mem twist
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Very Ample ZChart Span exists coeff of mem twist 939e653bd620 construction uses the P2 M Ground Theory Heights  Heights Kleiman Very Ample ZChart Span exists coeff of mem twist 939e653bd620 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZChartSpan.lean#L33-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZChartSpan.lean#L33-L60

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsVeryAmpleZFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZChartSpan
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
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZChartSpan
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
omit [Module S E] [IsScalarTower S Ω E]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZChartSpan_exists_coeff_of_mem_twist_939e653bd620 (F : SubSystem S x E) (Q : SubSystem S x Ω) (I : Chart x) (g : Finset E)
    (hg : F.sub I ≤ Submodule.span (chartRing S x I) (g : Set E)) {z : E} (hz : z ∈ (F.twist Q).sub I) :
    ∃ γ : E → Ω, (∀ y ∈ g, γ y ∈ Q.sub I) ∧ z = ∑ y ∈ g, γ y • y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«VeryAmpleZChartSpan».«exists_coeff_of_mem_twist» := P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZChartSpan_exists_coeff_of_mem_twist_939e653bd620
