-- Prove2me | Theorems.Thm_ThreeSum_LightResidueHistogram_time_bound
-- name    : ThreeSum.LightResidueHistogram.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:27:24.05921+00:00
-- url     : https://prove2.me/theorems/155252c0-76b5-4b13-abb4-c65114a986ec
-- title:
--   Light Residue Histogram: time bound
-- statement:
--   The Light Residue Histogram construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightResidueHistogram.lean#L176-L180
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightResidueHistogram.lean#L176-L180

import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_LightHistogram
import Definitions.Def_Submission_ThreeSum_CyclicFold
import Definitions.Def_Submission_ThreeSum_LightResidueHistogram
set_option autoImplicit false
open ThreeSum ThreeSum.LightResidueHistogram
open Light Finset ThreeSum.LightResidues ThreeSum.LightHistogram
open ThreeSum.CyclicFold ThreeSum.Karatsuba
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightResidueHistogram.time_bound (n cap U : ℕ) :
    time n cap U ≤ 13 * cap + 131 * n * (Nat.log 2 (U + 1) + 1) + 53 := by sorry
