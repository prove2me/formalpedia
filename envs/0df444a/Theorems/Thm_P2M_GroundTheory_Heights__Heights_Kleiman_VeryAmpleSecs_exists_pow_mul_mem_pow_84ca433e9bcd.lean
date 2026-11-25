-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleSecs_exists_pow_mul_mem_pow_84ca433e9bcd
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleSecs_exists_pow_mul_mem_pow_84ca433e9bcd
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:03:11.704422+00:00
-- url     : https://prove2.me/theorems/e18bef25-4d7a-5cf0-ae67-510e49101959
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Very Ample Secs exists pow mul mem pow 84ca433e9bcd: P2 M Ground Theory Heights  Heights Kleiman Very Ample Secs exists pow mul mem pow 84ca433e9bcd
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Very Ample Secs exists pow mul mem pow 84ca433e9bcd construction uses the P2 M Ground Theory Heights  Heights Kleiman Very Ample Secs exists pow mul mem pow 84ca433e9bcd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleSecs.lean#L73-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleSecs.lean#L73-L100

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleSecsSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleSecs
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
open GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleSecs
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleSecs_exists_pow_mul_mem_pow_84ca433e9bcd {A : Subalgebra k Ω} {L : Submodule A Ω} {r : ℕ}
    {h : Fin (r + 1) → Ω} (hL : ∀ l, h l ∈ L) {j : Fin (r + 1)} (hj : h j ≠ 0) {t : Ω}
    (ht : t ∈ ampleBase (S := k) h j) : ∃ e, h j ^ e * t ∈ L ^ e := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«VeryAmpleSecs».«exists_pow_mul_mem_pow» := P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleSecs_exists_pow_mul_mem_pow_84ca433e9bcd
