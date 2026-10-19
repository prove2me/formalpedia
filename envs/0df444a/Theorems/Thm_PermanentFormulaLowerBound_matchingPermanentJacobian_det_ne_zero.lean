-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_matchingPermanentJacobian_det_ne_zero
-- name    : PermanentFormulaLowerBound.matchingPermanentJacobian_det_ne_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:43.235103+00:00
-- url     : https://prove2.me/theorems/dd2a6fd2-b3b8-41ed-90e4-a2f6e7b2939f
-- title:
--   PermanentFormulaLowerBound.matchingPermanentJacobian_det_ne_zero
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin

theorem PermanentFormulaLowerBound.matchingPermanentJacobian_det_ne_zero
    {ell m : ℕ} (p q : Fin m → ℂ)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hm : m ≤ 2 ^ ell) (hroom : 2 * ell < m) :
    (matchingPermanentJacobian (ell := ell) p q).det ≠ 0 := by sorry
