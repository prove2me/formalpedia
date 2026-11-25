-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_exists_pow_mul_mem_ampleRing_b9b40574ef39
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_exists_pow_mul_mem_ampleRing_b9b40574ef39
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T06:35:01.734877+00:00
-- url     : https://prove2.me/theorems/011dd5ab-e75e-4869-aa62-63d377c03d07
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt exists pow mul mem ample Ring b9b40574ef39: P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt exists pow mul mem ample Ring b9b4
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt exists pow mul mem ample Ring b9b40574ef39 construction uses the P2 M Ground Theory Heights  Heights Kleiman Graph Closed Alt exists pow mul mem ample Ring b9b40574ef39 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PGraphClosedLocal.lean#L127-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PGraphClosedLocal.lean#L127-L159

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_exists_pow_mul_mem_ampleRing_b9b40574ef39 (H : SubSystem S x Ω) (h b : Ω) (J : Chart x)
    (hb : b ∈ ampleRing H 1 h)
    (hbJ : ∀ I : Chart x, ∃ e : ℕ,
      b ^ e * (xProd I ^ J.1.card / xProd J ^ I.1.card) ∈ ampleChart H 1 h I)
    {c : Ω} (hc : c ∈ chartRing S x J) : ∃ e : ℕ, b ^ e * c ∈ ampleRing H 1 h := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«GraphClosedAlt».«exists_pow_mul_mem_ampleRing» := P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_exists_pow_mul_mem_ampleRing_b9b40574ef39
