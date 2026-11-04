-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverLocal_first_moment
-- name    : ThreeSum.TernaryCoverLocal.first_moment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:47:17.10395+00:00
-- url     : https://prove2.me/theorems/c8d923ac-2116-411e-8168-f3769e2397b7
-- title:
--   Ternary Cover Local: first moment
-- statement:
--   The actual fixed-type graph retains at least three quarters of its
--   raw first moment.  No joint-type or graph independence hypothesis occurs.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverLocal.lean#L134-L150
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverLocal.lean#L134-L150

import Definitions.Def_Submission_ThreeSum_TernaryJointType
import Definitions.Def_Submission_ThreeSum_TernaryCoverTrimming
import Definitions.Def_Submission_ThreeSum_TernaryCoverFibers
import Definitions.Def_Submission_ThreeSum_TernaryCoverRetained
import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverLocal
open Finset TernaryJointType TernaryCoverHashes
open scoped BigOperators
variable {L p : ℕ}
variable [Fact (Nat.Prime p)]

theorem ThreeSum.TernaryCoverLocal.first_moment (α π : DigitType) (B : ℕ) (a b : ZMod p)
    (hB : 8 * (p + (fieldVertices L p α).card) ≤ B * p) :
    3 * Fintype.card (LocalEdge L α π) * Fintype.card (Coordinate (Fin L) → ZMod p) ≤
      4 * p ^ 2 * (∑ w : Coordinate (Fin L) → ZMod p, hitCount α π B w a b) := by sorry
