-- Prove2me | Theorems.Thm_ThreeSum_TernaryPrincipalDimensions_actual_bank_prefix_bound
-- name    : ThreeSum.TernaryPrincipalDimensions.actual_bank_prefix_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:56:31.176054+00:00
-- url     : https://prove2.me/theorems/872af5a0-14f9-4cd6-ac66-fa42cba2f5b1
-- title:
--   Ternary Principal Dimensions: actual bank prefix bound
-- statement:
--   The Ternary Principal Dimensions construction uses the actual bank prefix bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPrincipalDimensions.lean#L78-L89
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPrincipalDimensions.lean#L78-L89

import Definitions.Def_Submission_ThreeSum_TernaryFiniteLedger
import Definitions.Def_Submission_ThreeSum_TernaryPrincipalDimensions
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPrincipalDimensions
open Real TernaryParameters TernaryEntropyRates TernaryDimensionBounds
open TernaryCoverScale TernaryLocalParameters TernaryFiniteLedger

theorem ThreeSum.TernaryPrincipalDimensions.actual_bank_prefix_bound {m n j : ℕ} (hm : 0 < m) (hn : 1 < n)
    (hj : j ≤ radixLength m n) :
    (bankSize m j : ℝ) ≤ Real.exp ((fixedLength m : ℝ)*Real.log 2*bankEntropy)*
      (n : ℝ)^bankCharge m := by sorry
