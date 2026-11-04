-- Prove2me | Theorems.Thm_ThreeSumApsp_eventually_le_rpow
-- name    : ThreeSumApsp.eventually_le_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:10:07.98406+00:00
-- url     : https://prove2.me/theorems/fca65519-e599-4c2a-8448-ed16417d4f2f
-- title:
--   Three Sum Apsp: eventually le rpow
-- statement:
--   Every constant is eventually at most `n ^ η`, for `η > 0`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/Powers.lean#L39-L40
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/Powers.lean#L39-L40

import Definitions.Def_Submission_ThreeSumApsp_Util_Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp

theorem ThreeSumApsp.eventually_le_rpow (c : ℝ) {η : ℝ} (hη : 0 < η) : ∀ᶠ n : ℕ in atTop, c ≤ (n : ℝ) ^ η := by sorry
