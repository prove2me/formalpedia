-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedBankAssembly_layout
-- name    : ThreeSum.LightWeightedBankAssembly.layout
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:57:11.223659+00:00
-- url     : https://prove2.me/theorems/351f0e08-69db-4051-844f-08635ebecbbd
-- title:
--   Light Weighted Bank Assembly: layout
-- statement:
--   The Light Weighted Bank Assembly construction uses the layout property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankResources.lean#L51-L57
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankResources.lean#L51-L57

import Definitions.Def_Submission_Weighted_BankAssembly
import Definitions.Def_Submission_Weighted_BankResources
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedBankAssembly

theorem ThreeSum.LightWeightedBankAssembly.layout (a n N : ℕ) :
    a+n≤keyBase a n ∧ keyBase a n+4*n≤powersBase a n ∧
    powersBase a n+(2*N+1)≤fBase a n N ∧
    fBase a n N+(N+1)*n≤gBase a n N ∧
    gBase a n N+(N+1)*n≤hBase a n N ∧
    hBase a n N+(N+1)*n≤space a n N := by sorry
