-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_div_pow_mem_of_mem_pow_0ff2638b160f
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_div_pow_mem_of_mem_pow_0ff2638b160f
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:00:15.056251+00:00
-- url     : https://prove2.me/theorems/4f8212a6-fd03-4db3-b1c1-4ca628b17518
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman div pow mem of mem pow 0ff2638b160f: P2 M Ground Theory Heights  Heights Kleiman div pow mem of mem pow 0ff2638b160f
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman div pow mem of mem pow 0ff2638b160f construction uses the P2 M Ground Theory Heights  Heights Kleiman div pow mem of mem pow 0ff2638b160f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleTwistGenerated.lean#L154-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleTwistGenerated.lean#L154-L168

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_div_pow_mem_of_mem_pow_0ff2638b160f {B : Subalgebra k Ω} {T : Set Ω} {s : Ω}
    (hT : ∀ y ∈ T, y / s ∈ B) : ∀ n : ℕ, ∀ y ∈ T ^ n, y / s ^ n ∈ B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«div_pow_mem_of_mem_pow» := P2M_GroundTheory_Heights__Heights_Kleiman_div_pow_mem_of_mem_pow_0ff2638b160f
