-- Prove2me | Theorems.Thm_Sendov_B22_24_P_pos
-- name    : Sendov.B22_24.P_pos
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:09:37.006642+00:00
-- url     : https://prove2.me/theorems/cdfaff11-aa66-440a-95a2-a4fafcdcbfec
-- title:
--   B22 24: P pos
-- statement:
--   The certificate: `17 ^ 20 * P α` is a positive combination of `αʲ (17-α)^(20-j)`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree22_24.lean#L88-L141
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree22_24.lean#L88-L141

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree22_24
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B22_24
set_option maxHeartbeats 2000000

theorem Sendov.B22_24.P_pos {α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 23 / 2) :
    0 < 72676691260477709153931 + 243335498910644300539743 * α + 365647629606098581621152 * α ^ 2 + 324203560761134112575706 * α ^ 3 + 187220150267586036026391 * α ^ 4 + 72995868351568741088853 * α ^ 5 + 18997181712653091143742 * α ^ 6 + 2912276075526675669294 * α ^ 7 - 47524187765551795452 * α ^ 8 - 572344038827543054862 * α ^ 9 + 60958599043408078986 * α ^ 10 + 1608150216459380292 * α ^ 11 + 37160884428953616 * α ^ 12 - 4770728942909184 * α ^ 13 - 508194774105984 * α ^ 14 - 24843494479104 * α ^ 15 - 745526594304 * α ^ 16 - 14490071808 * α ^ 17 - 179034112 * α ^ 18 - 1285120 * α ^ 19 - 4096 * α ^ 20 := by sorry
