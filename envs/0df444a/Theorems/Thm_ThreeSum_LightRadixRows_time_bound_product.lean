-- Prove2me | Theorems.Thm_ThreeSum_LightRadixRows_time_bound_product
-- name    : ThreeSum.LightRadixRows.time_bound_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:18:24.397692+00:00
-- url     : https://prove2.me/theorems/51092958-c7b0-408e-bad6-b4309f8bc434
-- title:
--   Light Radix Rows: time bound product
-- statement:
--   The Light Radix Rows construction uses the time bound product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightRadixRows.lean#L142-L145
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightRadixRows.lean#L142-L145

import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Definitions.Def_Submission_ThreeSum_LightReportingAffine
import Definitions.Def_Submission_ThreeSum_LightRadixRows
set_option autoImplicit false
open ThreeSum ThreeSum.LightRadixRows
open Light RadixKeyLists
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightRadixRows.time_bound_product (m n : ℕ) (hn : 0 < n) : time m n ≤ 130*m*n+20 := by sorry
