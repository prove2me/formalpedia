-- Prove2me | Theorems.Thm_ThreeSum_TernaryTypeLowerBound_partition_cap_le_prime
-- name    : ThreeSum.TernaryTypeLowerBound.partition_cap_le_prime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:59:37.177939+00:00
-- url     : https://prove2.me/theorems/01fca087-ffab-4a33-bf5b-d66fa0d004d4
-- title:
--   Ternary Type Lower Bound: partition cap le prime
-- statement:
--   Consequently the basic prime-size guard also pays every output partition.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTypeLowerBound.lean#L110-L115
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTypeLowerBound.lean#L110-L115

import Definitions.Def_Submission_ThreeSum_TernaryCoverOutputCap
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryTypeLowerBound
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryTypeLowerBound
open Finset TernaryJointType TernaryCoverLocal

theorem ThreeSum.TernaryTypeLowerBound.partition_cap_le_prime {L : ℕ} (π : DigitType)
    (htotal : π 0+π 1+π 2 = L) (hspace : 2*(π 1)+3*(π 2) ≤ L)
    (P : ℕ) (hP : (vertices L π).card*(2^(π 1)*3^(π 2)) ≤ P^2) :
    2^(π 1)*3^(π 2) ≤ P := by sorry
