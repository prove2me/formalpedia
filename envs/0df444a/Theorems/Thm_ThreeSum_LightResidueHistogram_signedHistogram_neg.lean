-- Prove2me | Theorems.Thm_ThreeSum_LightResidueHistogram_signedHistogram_neg
-- name    : ThreeSum.LightResidueHistogram.signedHistogram_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:54:54.422448+00:00
-- url     : https://prove2.me/theorems/dbfcc089-d003-40da-94f1-05578085561e
-- title:
--   Light Residue Histogram: signed Histogram neg
-- statement:
--   Negating the original integers supplies the reversal needed by a
--   correlation, without a separate reverse-array operation.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightResidueHistogram.lean#L28-L31
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightResidueHistogram.lean#L28-L31

import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_LightHistogram
import Definitions.Def_Submission_ThreeSum_CyclicFold
import Definitions.Def_Submission_ThreeSum_LightResidueHistogram
set_option autoImplicit false
open ThreeSum ThreeSum.LightResidueHistogram
open Light Finset ThreeSum.LightResidues ThreeSum.LightHistogram
open ThreeSum.CyclicFold ThreeSum.Karatsuba
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightResidueHistogram.signedHistogram_neg (p : ℕ) (values : ℕ → ℤ) (n : ℕ) (z : ZMod p) :
    signedHistogram p (-1) values n z = signedHistogram p 1 values n (-z) := by sorry
