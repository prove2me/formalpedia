-- Prove2me | Theorems.Thm_ThreeSum_WeightedBankCanonical_read_of_seg
-- name    : ThreeSum.WeightedBankCanonical.read_of_seg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:58:25.934953+00:00
-- url     : https://prove2.me/theorems/ff547162-572a-4cbb-9a72-29d23d3d4faf
-- title:
--   Weighted Bank Canonical: read of seg
-- statement:
--   The actual enumerator's segment is exactly the assembler's physical code
--   premise, in the same order.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankCanonical.lean#L60-L65
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankCanonical.lean#L60-L65

import Definitions.Def_Submission_Weighted_BankStageModel
import Definitions.Def_Submission_Weighted_BankEnumeration
import Definitions.Def_Submission_Weighted_BankCanonical
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedBankCanonical
open ThreeSum.TernaryJointType ThreeSum.WeightedEnumeration
open ThreeSum.WeightedAddresses ThreeSum.WeightedBankEnumeration ThreeSum.WeightedBankStageModel
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 2000000

theorem ThreeSum.WeightedBankCanonical.read_of_seg {N T a : ℕ} (μ : ℕ→ℤ)
    (hseg : Light.Seg μ a ((codes N T).map (fun c => (c : ℤ)))) :
    ∀ j<(codes N T).length, μ (a+j)=(address ((enumeration N T).word j) : ℤ) := by sorry
