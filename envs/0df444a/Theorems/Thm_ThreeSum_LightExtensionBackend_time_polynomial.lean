-- Prove2me | Theorems.Thm_ThreeSum_LightExtensionBackend_time_polynomial
-- name    : ThreeSum.LightExtensionBackend.time_polynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:58:16.742371+00:00
-- url     : https://prove2.me/theorems/149b8f94-5b4b-4c7d-b48f-6a36a0d31621
-- title:
--   Light Extension Backend: time polynomial
-- statement:
--   The complete actual field construction and physical menu construction
--   cost a fixed polynomial, independent of every absolute memory address.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionBackendBudget.lean#L10-L27
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionBackendBudget.lean#L10-L27

import Definitions.Def_Submission_ThreeSum_LightExtensionBackend
import Definitions.Def_Submission_ThreeSum_LightIrreducibleBudget
import Definitions.Def_Submission_ThreeSum_LightExtensionMenuBudget
import Definitions.Def_Submission_ThreeSum_LightExtensionBackendBudget
import Theorems.Thm_ThreeSum_LightExtensionMenuMatrix_time_polynomial

set_option autoImplicit false
open ThreeSum ThreeSum.LightExtensionBackend
set_option maxHeartbeats 2000000

theorem ThreeSum.LightExtensionBackend.time_polynomial (F : LightExtensionFactorPredicate.Layout)
    (q J a b h r prod sum : ℕ) :
    time F q J a b h r prod sum (LightIrreducibleFinder.uniformFactorTime F.dim F.p q) ≤
      10000000000*(F.dim+F.p+q+J+2)^10 := by sorry
