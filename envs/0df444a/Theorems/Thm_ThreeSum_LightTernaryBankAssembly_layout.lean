-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryBankAssembly_layout
-- name    : ThreeSum.LightTernaryBankAssembly.layout
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:00:40.56411+00:00
-- url     : https://prove2.me/theorems/26a4c3ca-5e04-4500-8fb1-2ebea8b97149
-- title:
--   Light Ternary Bank Assembly: layout
-- statement:
--   The Light Ternary Bank Assembly construction uses the layout property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryBankResources.lean#L46-L52
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryBankResources.lean#L46-L52

import Definitions.Def_Submission_ThreeSum_LightTernaryBankAssembly
import Definitions.Def_Submission_ThreeSum_LightTernaryBankResources
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryBankAssembly

theorem ThreeSum.LightTernaryBankAssembly.layout (a n N : ℕ) :
    a+n≤keyBase a n ∧ keyBase a n+4*n≤powersBase a n ∧
    powersBase a n+(2*N+1)≤fBase a n N ∧
    fBase a n N+(N+1)*n≤gBase a n N ∧
    gBase a n N+(N+1)*n≤hBase a n N ∧
    hBase a n N+(N+1)*n≤space a n N := by sorry
