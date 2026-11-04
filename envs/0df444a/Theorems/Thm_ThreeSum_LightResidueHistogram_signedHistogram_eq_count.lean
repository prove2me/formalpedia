-- Prove2me | Theorems.Thm_ThreeSum_LightResidueHistogram_signedHistogram_eq_count
-- name    : ThreeSum.LightResidueHistogram.signedHistogram_eq_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:13:18.59317+00:00
-- url     : https://prove2.me/theorems/c83cb0ce-d7d6-4d96-adc7-4634017c346a
-- title:
--   Light Residue Histogram: signed Histogram eq count
-- statement:
--   The Light Residue Histogram construction uses the signed Histogram eq count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightResidueHistogram.lean#L58-L66
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightResidueHistogram.lean#L58-L66

import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_LightHistogram
import Definitions.Def_Submission_ThreeSum_CyclicFold
import Definitions.Def_Submission_ThreeSum_LightResidueHistogram
set_option autoImplicit false
open ThreeSum ThreeSum.LightResidueHistogram
open Light Finset ThreeSum.LightResidues ThreeSum.LightHistogram
open ThreeSum.CyclicFold ThreeSum.Karatsuba
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightResidueHistogram.signedHistogram_eq_count {p : ℕ} [NeZero p]
    (c : ℤ) (values : ℕ → ℤ) (n r : ℕ) (hr : r < p) :
    signedHistogram p c values n (r : ZMod p) =
      count (fun i => residue p c (values i)) r n := by sorry
