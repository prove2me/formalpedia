-- Prove2me | Theorems.Thm_ThreeSum_TernaryPrincipalDimensions_prefix_linear_bound
-- name    : ThreeSum.TernaryPrincipalDimensions.prefix_linear_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:00:17.540948+00:00
-- url     : https://prove2.me/theorems/7918267f-efa3-4f06-936a-575a10cb2e66
-- title:
--   Ternary Principal Dimensions: prefix linear bound
-- statement:
--   The Ternary Principal Dimensions construction uses the prefix linear bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPrincipalDimensions.lean#L20-L40
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPrincipalDimensions.lean#L20-L40

import Definitions.Def_Submission_ThreeSum_TernaryFiniteLedger
import Definitions.Def_Submission_ThreeSum_TernaryPrincipalDimensions
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPrincipalDimensions
open Real TernaryParameters TernaryEntropyRates TernaryDimensionBounds
open TernaryCoverScale TernaryLocalParameters TernaryFiniteLedger

theorem ThreeSum.TernaryPrincipalDimensions.prefix_linear_bound {M n j : ℕ} (hM : 1 < M) (hn : 1 < n)
    (hj : j ≤ Nat.clog M (n^2)) {a : ℝ} (ha : 0 ≤ a) :
    (j : ℝ)*a ≤ a+(2*a/Real.log M)*Real.log n := by sorry
