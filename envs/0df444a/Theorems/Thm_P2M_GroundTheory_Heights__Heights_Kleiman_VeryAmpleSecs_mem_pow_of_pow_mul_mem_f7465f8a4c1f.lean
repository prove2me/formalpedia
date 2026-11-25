-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleSecs_mem_pow_of_pow_mul_mem_f7465f8a4c1f
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleSecs_mem_pow_of_pow_mul_mem_f7465f8a4c1f
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:00:18.564256+00:00
-- url     : https://prove2.me/theorems/400f2a93-da6f-4d0b-b03d-4e51a8cf26b3
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Very Ample Secs mem pow of pow mul mem f7465f8a4c1f: P2 M Ground Theory Heights  Heights Kleiman Very Ample Secs mem pow of pow mul mem f7465f8a4c1f
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Very Ample Secs mem pow of pow mul mem f7465f8a4c1f construction uses the P2 M Ground Theory Heights  Heights Kleiman Very Ample Secs mem pow of pow mul mem f7465f8a4c1f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleSecs.lean#L45-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleSecs.lean#L45-L71

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleSecs_mem_pow_of_pow_mul_mem_f7465f8a4c1f {A : Type*} [CommRing A] [Algebra A Ω] {L Q : Submodule A Ω}
    (hLQ : L * Q = 1) {r : ℕ} {h : Fin (r + 1) → Ω} (hL : Submodule.span A (Set.range h) = L)
    {s : Ω} {n : ℕ} (hs : ∀ j, ∃ e, h j ^ e * s ∈ L ^ (n + e)) : s ∈ L ^ n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«VeryAmpleSecs».«mem_pow_of_pow_mul_mem» := P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleSecs_mem_pow_of_pow_mul_mem_f7465f8a4c1f
