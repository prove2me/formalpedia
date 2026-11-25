-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_of_pow_mul_mem_ead8bf589589
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_mem_of_pow_mul_mem_ead8bf589589
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:22:22.433832+00:00
-- url     : https://prove2.me/theorems/0bb0c367-e5c3-4727-bed7-05171f70af00
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman mem of pow mul mem ead8bf589589: P2 M Ground Theory Heights  Heights Kleiman mem of pow mul mem ead8bf589589
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman mem of pow mul mem ead8bf589589 construction uses the P2 M Ground Theory Heights  Heights Kleiman mem of pow mul mem ead8bf589589 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleTwistGenerated.lean#L129-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleTwistGenerated.lean#L129-L152

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_mem_of_pow_mul_mem_ead8bf589589 {B : Subalgebra k Ω} {n : ℕ} {a b : Fin n → Ω} {z : Ω}
    (ha : ∀ i, a i ∈ B) (hb : ∀ i, b i ∈ B) (hab : ∑ i, a i * b i = 1)
    (hz : ∀ i, ∃ E : ℕ, b i ^ E * z ∈ B) : z ∈ B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«mem_of_pow_mul_mem» := P2M_GroundTheory_Heights__Heights_Kleiman_mem_of_pow_mul_mem_ead8bf589589
