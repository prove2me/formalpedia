-- Prove2me | Theorems.Thm_ThreeSum_LightResidueHistogram_padded_histogram_getD
-- name    : ThreeSum.LightResidueHistogram.padded_histogram_getD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:55:08.029858+00:00
-- url     : https://prove2.me/theorems/f191a21e-c537-452f-8e04-0221dce23062
-- title:
--   Light Residue Histogram: padded histogram get D
-- statement:
--   This equality holds at every index, including the zero padding.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightResidueHistogram.lean#L80-L89
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightResidueHistogram.lean#L80-L89

import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_LightHistogram
import Definitions.Def_Submission_ThreeSum_CyclicFold
import Definitions.Def_Submission_ThreeSum_LightResidueHistogram
set_option autoImplicit false
open ThreeSum ThreeSum.LightResidueHistogram
open Light Finset ThreeSum.LightResidues ThreeSum.LightHistogram
open ThreeSum.CyclicFold ThreeSum.Karatsuba
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightResidueHistogram.padded_histogram_getD {p : ℕ} [NeZero p]
    (c : ℤ) (values : ℕ → ℤ) (n cap r : ℕ) :
    (padTo cap (vector p (signedHistogram p c values n))).getD r 0 =
      (count (fun i => residue p c (values i)) r n : ℤ) := by sorry
