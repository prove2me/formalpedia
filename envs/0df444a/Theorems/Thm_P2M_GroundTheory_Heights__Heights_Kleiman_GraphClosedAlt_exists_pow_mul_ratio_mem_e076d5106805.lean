-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_exists_pow_mul_ratio_mem_e076d5106805
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_exists_pow_mul_ratio_mem_e076d5106805
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:57:22.264521+00:00
-- url     : https://prove2.me/theorems/55bcf7dc-0835-59bd-b994-efe408cada9b
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt exists pow mul ratio mem e076d5106805: P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt exists pow mul ratio mem e076d5106805
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt exists pow mul ratio mem e076d5106805 construction uses the P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt exists pow mul ratio mem e076d5106805 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PGraphClosedLocal.lean#L58-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PGraphClosedLocal.lean#L58-L87

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GeneratedTwistSysZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PGraphClosedLocal
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
open GroundTheory.Heights₂.Heights.Kleiman.GraphClosedAlt
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_exists_pow_mul_ratio_mem_e076d5106805 (I J : Chart x) {i₀ : Fin (N + 1)} (hi₀ : i₀ ∈ I.1)
    {i : Fin (N + 1)} (hi : i ∈ I.1 ∪ J.1) : ∃ e : ℕ,
    (xProd J ^ I.1.card / xProd I ^ J.1.card) ^ e * (x i₀ / x i) ∈ chartRing S x I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«GraphClosedAlt».«exists_pow_mul_ratio_mem» := P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_exists_pow_mul_ratio_mem_e076d5106805
