-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryWantedBudget_time_polynomial
-- name    : ThreeSum.LightTernaryWantedBudget.time_polynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:08:50.325086+00:00
-- url     : https://prove2.me/theorems/5ebbf964-2981-47fc-aed1-fffe31ff07f0
-- title:
--   Light Ternary Wanted Budget: time polynomial
-- statement:
--   With a fixed native radix and exponentially bounded target magnitude,
--   the actual DFS spends only a quadratic polynomial in block count per fiber.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryWantedBudget.lean#L17-L39
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryWantedBudget.lean#L17-L39

import Definitions.Def_Submission_ThreeSum_LightTernaryWantedCanonical
import Definitions.Def_Submission_ThreeSum_LightTernaryWantedBudget
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryWantedBudget
open LightTernaryWantedCanonical

theorem ThreeSum.LightTernaryWantedBudget.time_polynomial (P C V A J : ℕ) (hC : 1 ≤ C)
    (hV : V ≤ A*(P+1)^J) :
    time P C V J ≤ 1000*(A+2*P+4)*(J+1)^2*C^J := by sorry
