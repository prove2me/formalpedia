-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedBankAssembly_space_eq
-- name    : ThreeSum.LightWeightedBankAssembly.space_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:51:18.147184+00:00
-- url     : https://prove2.me/theorems/2679297e-316f-4f8f-9482-e05854fabfcf
-- title:
--   Light Weighted Bank Assembly: space eq
-- statement:
--   The Light Weighted Bank Assembly construction uses the space eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankResources.lean#L47-L49
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankResources.lean#L47-L49

import Definitions.Def_Submission_Weighted_BankAssembly
import Definitions.Def_Submission_Weighted_BankResources
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedBankAssembly

theorem ThreeSum.LightWeightedBankAssembly.space_eq (a n N : ℕ) : space a n N=a+(3*N+8)*n+2*N+1 := by sorry
