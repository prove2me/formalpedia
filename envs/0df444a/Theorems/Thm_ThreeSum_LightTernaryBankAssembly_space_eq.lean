-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryBankAssembly_space_eq
-- name    : ThreeSum.LightTernaryBankAssembly.space_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:52:31.11993+00:00
-- url     : https://prove2.me/theorems/c2be7851-3352-4b85-bb76-b45d26aefe49
-- title:
--   Light Ternary Bank Assembly: space eq
-- statement:
--   The Light Ternary Bank Assembly construction uses the space eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryBankResources.lean#L42-L44
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryBankResources.lean#L42-L44

import Definitions.Def_Submission_ThreeSum_LightTernaryBankAssembly
import Definitions.Def_Submission_ThreeSum_LightTernaryBankResources
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryBankAssembly

theorem ThreeSum.LightTernaryBankAssembly.space_eq (a n N : ℕ) : space a n N=a+(3*N+8)*n+2*N+1 := by sorry
