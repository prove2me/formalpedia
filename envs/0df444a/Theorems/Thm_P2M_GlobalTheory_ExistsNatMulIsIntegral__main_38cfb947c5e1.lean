-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ExistsNatMulIsIntegral__main_38cfb947c5e1
-- name    : P2M_GlobalTheory_ExistsNatMulIsIntegral__main_38cfb947c5e1
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:07:42.591805+00:00
-- url     : https://prove2.me/theorems/55a3a2a5-b30d-4668-a5a3-e3001f8858a0
-- title:
--   P2 M Global Theory Exists Nat Mul Is Integral  main 38cfb947c5e1: P2 M Global Theory Exists Nat Mul Is Integral  main 38cfb947c5e1
-- statement:
--   The P2 M Global Theory Exists Nat Mul Is Integral  main 38cfb947c5e1 construction uses the P2 M Global Theory Exists Nat Mul Is Integral  main 38cfb947c5e1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsNatMulIsIntegral.lean#L16-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsNatMulIsIntegral.lean#L16-L41

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

theorem P2M_GlobalTheory_ExistsNatMulIsIntegral__main_38cfb947c5e1 : ∀ {E W : Type} [inst : Field E] [NumberField E] [inst_2 : AddCommGroup W] [inst_3 : Module E W]
    [inst_4 : Module (NumberField.RingOfIntegers E) W] [IsScalarTower (NumberField.RingOfIntegers E) E W]
    (L : Submodule (NumberField.RingOfIntegers E) W),
    ∀ x ∈ Submodule.span E (↑L : Set W), ∃ (k : ℕ), (0 : ℕ) < k ∧ k • x ∈ L := by sorry

alias «GlobalTheory».«ExistsNatMulIsIntegral₂».«main» := P2M_GlobalTheory_ExistsNatMulIsIntegral__main_38cfb947c5e1
