-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedBankAssembly_word_bounds
-- name    : ThreeSum.LightWeightedBankAssembly.word_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:51:17.052195+00:00
-- url     : https://prove2.me/theorems/980135c3-0475-46a1-a56a-83ec213e634d
-- title:
--   Light Weighted Bank Assembly: word bounds
-- statement:
--   The Light Weighted Bank Assembly construction uses the word bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankResources.lean#L64-L72
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankResources.lean#L64-L72

import Definitions.Def_Submission_Weighted_BankAssembly
import Definitions.Def_Submission_Weighted_BankResources
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedBankAssembly

theorem ThreeSum.LightWeightedBankAssembly.word_bounds (a n N V : ℕ) :
    space a n N≤word a n N V ∧ n+2^(2*N+1)+16≤word a n N V ∧
    2*N+3≤word a n N V ∧ 4*(4^N*V)+3≤word a n N V ∧
    valueBound N V≤word a n N V ∧ 4*(4^N*valueBound N V)+3≤word a n N V := by sorry
