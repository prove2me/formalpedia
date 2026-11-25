-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_pow_mul_mem_of_mem_span_1463fb00a4ce
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_exists_pow_mul_mem_of_mem_span_1463fb00a4ce
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:09:08.638609+00:00
-- url     : https://prove2.me/theorems/333e1879-1e92-596a-836e-81302b944a80
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman exists pow mul mem of mem span 1463fb00a4ce: P2 M Ground Theory Heights  Heights Kleiman exists pow mul mem of mem span 1463fb00a4ce
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman exists pow mul mem of mem span 1463fb00a4ce construction uses the P2 M Ground Theory Heights  Heights Kleiman exists pow mul mem of mem span 1463fb00a4ce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleTwistGenerated.lean#L170-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleTwistGenerated.lean#L170-L200

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_exists_pow_mul_mem_of_mem_span_1463fb00a4ce {B : Subalgebra k Ω} {J : Chart x} {T : Set Ω}
    {s b z : Ω} {n : ℕ} (hs : s ≠ 0) (hb : b ∈ B) (hT : ∀ y ∈ T, y / s ^ n ∈ B)
    (hcoef : ∀ c ∈ chartRing k x J, ∃ E : ℕ, b ^ E * c ∈ B)
    (hz : z * s ^ n ∈ Submodule.span (chartRing k x J) T) : ∃ E : ℕ, b ^ E * z ∈ B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«exists_pow_mul_mem_of_mem_span» := P2M_GroundTheory_Heights__Heights_Kleiman_exists_pow_mul_mem_of_mem_span_1463fb00a4ce
