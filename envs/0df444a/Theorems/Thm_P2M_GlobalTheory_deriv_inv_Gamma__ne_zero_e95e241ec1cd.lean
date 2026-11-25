-- Prove2me | Theorems.Thm_P2M_GlobalTheory_deriv_inv_Gamma__ne_zero_e95e241ec1cd
-- name    : P2M_GlobalTheory_deriv_inv_Gamma__ne_zero_e95e241ec1cd
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:12:00.891215+00:00
-- url     : https://prove2.me/theorems/d050cbaa-7076-43a0-8074-ac71370cc58f
-- title:
--   P2 M Global Theory deriv inv Gamma  ne zero e95e241ec1cd: P2 M Global Theory deriv inv Gamma  ne zero e95e241ec1cd
-- statement:
--   The P2 M Global Theory deriv inv Gamma  ne zero e95e241ec1cd construction uses the P2 M Global Theory deriv inv Gamma  ne zero e95e241ec1cd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/CompletedLFunctionNeZeroOfReNonpos.lean#L31-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/CompletedLFunctionNeZeroOfReNonpos.lean#L31-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_CompletedLFunctionNeZeroOfReNonpos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory

theorem P2M_GlobalTheory_deriv_inv_Gamma__ne_zero_e95e241ec1cd (n : ℕ) :
    deriv (fun s : ℂ => (Gammaℝ s)⁻¹) (-(2 * n)) ≠ 0 := by sorry

alias «GlobalTheory».«deriv_inv_Gammaℝ_ne_zero» := P2M_GlobalTheory_deriv_inv_Gamma__ne_zero_e95e241ec1cd
