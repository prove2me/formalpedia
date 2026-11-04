-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryMomentAccumulate_other_row_kept
-- name    : ThreeSum.LightTernaryMomentAccumulate.other_row_kept
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:56:46.206045+00:00
-- url     : https://prove2.me/theorems/878cef0a-4fc1-41fd-8f60-bfa36d35d546
-- title:
--   Light Ternary Moment Accumulate: other row kept
-- statement:
--   An accumulation writes one matrix row and preserves every other row,
--   including rows already completed by earlier channels.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryMomentAccumulate.lean#L66-L79
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryMomentAccumulate.lean#L66-L79

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightTernaryMomentAccumulate
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryMomentAccumulate
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightTernaryMomentAccumulate.other_row_kept {μ ν : ℕ→ℤ} {matrix count k l : ℕ}
    (hkeep : SameOutside μ ν (matrix+k*count) count) (hkl : k≠l) :
    ∀ i<count, ν (matrix+l*count+i)=μ (matrix+l*count+i) := by sorry
