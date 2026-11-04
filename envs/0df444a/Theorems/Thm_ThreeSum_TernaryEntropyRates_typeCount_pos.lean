-- Prove2me | Theorems.Thm_ThreeSum_TernaryEntropyRates_typeCount_pos
-- name    : ThreeSum.TernaryEntropyRates.typeCount_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:00:00.428531+00:00
-- url     : https://prove2.me/theorems/06b2ed81-6bfe-475e-8ecf-e4ba16b5e217
-- title:
--   Ternary Entropy Rates: type Count pos
-- statement:
--   The Ternary Entropy Rates construction uses the type Count pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEntropyRates.lean#L29-L33
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEntropyRates.lean#L29-L33

import Definitions.Def_Submission_ThreeSum_TernaryParameters
import Definitions.Def_Submission_ThreeSum_TernaryCoverScale
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
import Definitions.Def_Submission_ThreeSum_TernaryEntropyRates
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryEntropyRates
open Filter Real
open scoped Topology
open TernaryJointType TernaryCoverLocal TernaryLocalParameters TernaryCoverScale
set_option maxRecDepth 10000

theorem ThreeSum.TernaryEntropyRates.typeCount_pos {N r1 r2 : ℕ} (h1 : r1+r2 ≤ N) (m : ℕ) :
    0 < typeCount N r1 r2 m := by sorry
