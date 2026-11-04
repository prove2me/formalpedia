-- Prove2me | Theorems.Thm_ThreeSum_TernaryEntropyRates_typeCount_bits_tendsto
-- name    : ThreeSum.TernaryEntropyRates.typeCount_bits_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:01:05.444733+00:00
-- url     : https://prove2.me/theorems/7c542051-2213-417b-91d0-711c008ea390
-- title:
--   Ternary Entropy Rates: type Count bits tendsto
-- statement:
--   The Ternary Entropy Rates construction uses the type Count bits tendsto property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEntropyRates.lean#L39-L55
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEntropyRates.lean#L39-L55

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

theorem ThreeSum.TernaryEntropyRates.typeCount_bits_tendsto {N r1 r2 : ℕ} (hN : 0 < N)
    (h2 : r2 < N) (h1 : r1+r2 ≤ N) :
    Tendsto (fun m : ℕ => Real.log (typeCount N r1 r2 m : ℝ)/
      (((N*m : ℕ) : ℝ)*Real.log 2)) atTop (𝓝 (splitBits N r1 r2)) := by sorry
