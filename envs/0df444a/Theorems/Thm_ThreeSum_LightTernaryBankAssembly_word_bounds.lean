-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryBankAssembly_word_bounds
-- name    : ThreeSum.LightTernaryBankAssembly.word_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:52:51.201933+00:00
-- url     : https://prove2.me/theorems/e4e2aae4-1d43-48f3-8570-95cec126f1c2
-- title:
--   Light Ternary Bank Assembly: word bounds
-- statement:
--   The Light Ternary Bank Assembly construction uses the word bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryBankResources.lean#L59-L67
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryBankResources.lean#L59-L67

import Definitions.Def_Submission_ThreeSum_LightTernaryBankAssembly
import Definitions.Def_Submission_ThreeSum_LightTernaryBankResources
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryBankAssembly

theorem ThreeSum.LightTernaryBankAssembly.word_bounds (a n N V : ℕ) :
    space a n N≤word a n N V ∧ n+2^(2*N+1)+16≤word a n N V ∧
    2*N+3≤word a n N V ∧ 4*(4^N*V)+3≤word a n N V ∧
    valueBound N V≤word a n N V ∧ 4*(4^N*valueBound N V)+3≤word a n N V := by sorry
