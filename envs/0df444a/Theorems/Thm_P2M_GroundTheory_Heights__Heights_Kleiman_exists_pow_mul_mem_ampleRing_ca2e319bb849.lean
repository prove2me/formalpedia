-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_pow_mul_mem_ampleRing_ca2e319bb849
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_exists_pow_mul_mem_ampleRing_ca2e319bb849
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:01:52.613687+00:00
-- url     : https://prove2.me/theorems/9eb86850-cac5-40fa-b9e4-66afdf028ca0
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman exists pow mul mem ample Ring ca2e319bb849: P2 M Ground Theory Heights  Heights Kleiman exists pow mul mem ample Ring ca2e319bb849
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman exists pow mul mem ample Ring ca2e319bb849 construction uses the P2 M Ground Theory Heights  Heights Kleiman exists pow mul mem ample Ring ca2e319bb849 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleTwistGenerated.lean#L106-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleTwistGenerated.lean#L106-L127

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsJoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefPlusAmple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleTwistGenerated
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
open scoped Pointwise
noncomputable section
universe u w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_exists_pow_mul_mem_ampleRing_ca2e319bb849 {L : SubSystem k x Ω} {hl b c : Ω} {J : Chart x}
    (hb : b ∈ ampleRing L 1 hl)
    (hbJ : ∀ I : Chart x, ∃ e : ℕ,
      b ^ e * (xProd I ^ J.1.card / xProd J ^ I.1.card) ∈ ampleChart L 1 hl I)
    (hc : c ∈ chartRing k x J) : ∃ E : ℕ, b ^ E * c ∈ ampleRing L 1 hl := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«exists_pow_mul_mem_ampleRing» := P2M_GroundTheory_Heights__Heights_Kleiman_exists_pow_mul_mem_ampleRing_ca2e319bb849
