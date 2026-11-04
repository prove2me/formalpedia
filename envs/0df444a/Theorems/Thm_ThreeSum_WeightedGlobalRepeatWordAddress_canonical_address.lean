-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalRepeatWordAddress_canonical_address
-- name    : ThreeSum.WeightedGlobalRepeatWordAddress.canonical_address
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:19:55.117628+00:00
-- url     : https://prove2.me/theorems/c114f580-4045-420d-81ba-ff49f9e1b091
-- title:
--   Weighted Global Repeat Word Address: canonical address
-- statement:
--   The executed scalar recurrence is exactly the canonical repeated local
--   word address used by the literal finite source/query model.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryRepeatWordAddress.lean#L32-L47
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryRepeatWordAddress.lean#L32-L47

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_LightTernaryRepeatWord
import Definitions.Def_Submission_Weighted_Global_TernaryCanonicalTupleCodes
import Definitions.Def_Submission_Weighted_Global_TernaryRepeatWordAddress
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalRepeatWordAddress
open ThreeSum.LightTernaryRepeatWord
open TernaryJointType
set_option maxHeartbeats 2000000

theorem ThreeSum.WeightedGlobalRepeatWordAddress.canonical_address {L : ℕ} (Q : TritWord L) (r : ℕ) :
    value (TernaryCodeSemantics.address Q) (4^L) r=
      TernaryCodeSemantics.address (WeightedGlobalRepeatedWords.canonical (fun _ : Fin r=>Q)) := by sorry
