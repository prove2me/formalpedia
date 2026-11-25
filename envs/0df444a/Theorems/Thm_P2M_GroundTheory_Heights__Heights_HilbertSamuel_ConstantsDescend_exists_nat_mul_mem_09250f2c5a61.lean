-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConstantsDescend_exists_nat_mul_mem_09250f2c5a61
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConstantsDescend_exists_nat_mul_mem_09250f2c5a61
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:19:00.194239+00:00
-- url     : https://prove2.me/theorems/f4a419f0-9718-41b5-9514-c6c0afb302b0
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Constants Descend exists nat mul mem 09250f2c5a61: P2 M Ground Theory Heights  Heights Hilbert Samuel Constants Descend exists nat mul mem 09250f2c5a
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Constants Descend exists nat mul mem 09250f2c5a61 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Constants Descend exists nat mul mem 09250f2c5a61 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PConstantsDescend.lean#L170-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PConstantsDescend.lean#L170-L195

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsConstantsDescend
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PConstantsDescend
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open Polynomial
open GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantsDescend

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConstantsDescend_exists_nat_mul_mem_09250f2c5a61 {Ω : Type*} [Field Ω] [CharZero Ω] (R : Subalgebra ℤ Ω) {x : Ω}
    (hx : x ∈ Algebra.adjoin ℚ (R : Set Ω)) : ∃ n : ℕ, 0 < n ∧ (n : Ω) * x ∈ R := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«ConstantsDescend».«exists_nat_mul_mem» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConstantsDescend_exists_nat_mul_mem_09250f2c5a61
