-- Prove2me | Theorems.Thm_ThreeSumApsp_isBigO_of_abs_le
-- name    : ThreeSumApsp.isBigO_of_abs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:02:39.489063+00:00
-- url     : https://prove2.me/theorems/da302706-e343-4078-9475-bb4c9706e804
-- title:
--   Three Sum Apsp: is Big O of abs le
-- statement:
--   A bound `|f n| ≤ C * g n` from some `n₀` on gives `f = O(g)`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/Powers.lean#L32-L36
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/Powers.lean#L32-L36

import Definitions.Def_Submission_ThreeSumApsp_Util_Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp

theorem ThreeSumApsp.isBigO_of_abs_le {f g : ℕ → ℝ} (C : ℝ) (n₀ : ℕ) (h : ∀ n, n₀ ≤ n → |f n| ≤ C * g n) :
    f =O[atTop] g := by sorry
