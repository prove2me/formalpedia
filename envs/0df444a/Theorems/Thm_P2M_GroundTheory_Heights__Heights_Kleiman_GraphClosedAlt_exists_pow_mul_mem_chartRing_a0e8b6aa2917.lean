-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_exists_pow_mul_mem_chartRing_a0e8b6aa2917
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_exists_pow_mul_mem_chartRing_a0e8b6aa2917
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:57:28.8936+00:00
-- url     : https://prove2.me/theorems/5450f310-dcb7-5179-948d-20d2247dbb20
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt exists pow mul mem chart Ring a0e8b6aa2917: P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt exists pow mul mem chart Ring a0e8
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt exists pow mul mem chart Ring a0e8b6aa2917 construction uses the P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt exists pow mul mem chart Ring a0e8b6aa2917 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PGraphClosedLocal.lean#L89-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PGraphClosedLocal.lean#L89-L125

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_exists_pow_mul_mem_chartRing_a0e8b6aa2917 (I J : Chart x) {z : Ω}
    (hz : z ∈ chartRing S x (chartUnion I J)) : ∃ e : ℕ,
    (xProd J ^ I.1.card / xProd I ^ J.1.card) ^ e * z ∈ chartRing S x I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«GraphClosedAlt».«exists_pow_mul_mem_chartRing» := P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_exists_pow_mul_mem_chartRing_a0e8b6aa2917
