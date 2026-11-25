-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ExistsNatMulIsIntegral__exists_nat_mul_isIntegral_373366b61ebd
-- name    : P2M_GlobalTheory_ExistsNatMulIsIntegral__exists_nat_mul_isIntegral_373366b61ebd
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:04:55.101786+00:00
-- url     : https://prove2.me/theorems/ccc7e941-12aa-484e-8c8a-d851ae29a1c6
-- title:
--   P2 M Global Theory Exists Nat Mul Is Integral  exists nat mul is Integral 373366b61ebd: P2 M Global Theory Exists Nat Mul Is Integral  exists nat mul is Integral 373366b61ebd
-- statement:
--   The P2 M Global Theory Exists Nat Mul Is Integral  exists nat mul is Integral 373366b61ebd construction uses the P2 M Global Theory Exists Nat Mul Is Integral  exists nat mul is Integral 373366b61ebd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsNatMulIsIntegral.lean#L7-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsNatMulIsIntegral.lean#L7-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsNatMulIsIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ExistsNatMulIsIntegral₂
open NumberField

theorem P2M_GlobalTheory_ExistsNatMulIsIntegral__exists_nat_mul_isIntegral_373366b61ebd {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ d : ℕ, 0 < d ∧ IsIntegral ℤ ((d : E) * c) := by sorry

alias «GlobalTheory».«ExistsNatMulIsIntegral₂».«exists_nat_mul_isIntegral» := P2M_GlobalTheory_ExistsNatMulIsIntegral__exists_nat_mul_isIntegral_373366b61ebd
