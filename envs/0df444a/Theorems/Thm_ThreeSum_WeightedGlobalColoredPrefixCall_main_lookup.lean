-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredPrefixCall_main_lookup
-- name    : ThreeSum.WeightedGlobalColoredPrefixCall.main_lookup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:19:27.437436+00:00
-- url     : https://prove2.me/theorems/1e7bc7f4-2957-446e-b7ad-9a1976e6ca22
-- title:
--   Weighted Global Colored Prefix Call: main lookup
-- statement:
--   The Weighted Global Colored Prefix Call construction uses the main lookup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredPrefixCall.lean#L36-L49
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredPrefixCall.lean#L36-L49

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryColoredSolver
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixInit
import Definitions.Def_Submission_Weighted_Global_TernaryColoredPrefixCall
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredPrefixCall
open Light LightWeightedGlobalColoredSolver
set_option maxHeartbeats 1500000
set_option maxRecDepth 24000

theorem ThreeSum.WeightedGlobalColoredPrefixCall.main_lookup (radix D E K bDigit a b scaleBase p R F m alpha2 alphaRank localQ L : ℕ)
    (raws : List ℤ) (words maps : List ℕ) (xl yl zl xr yr zr : List ℤ)
    (post : Program) (postMain : ℕ) :
    (program radix D E K bDigit a b scaleBase p R F m alpha2 alphaRank localQ L
      raws words maps xl yl zl xr yr zr post postMain)[252+post.length]?=
      some (body (252+postMain) m F p alpha2 alphaRank localQ R a b scaleBase L) := by sorry
