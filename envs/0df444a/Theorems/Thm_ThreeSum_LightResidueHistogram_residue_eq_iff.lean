-- Prove2me | Theorems.Thm_ThreeSum_LightResidueHistogram_residue_eq_iff
-- name    : ThreeSum.LightResidueHistogram.residue_eq_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:31:22.304705+00:00
-- url     : https://prove2.me/theorems/71ae13e9-6801-4b8a-ad1b-ddcdc5199c8e
-- title:
--   Light Residue Histogram: residue eq iff
-- statement:
--   The Light Residue Histogram construction uses the residue eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightResidueHistogram.lean#L46-L56
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightResidueHistogram.lean#L46-L56

import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_LightHistogram
import Definitions.Def_Submission_ThreeSum_CyclicFold
import Definitions.Def_Submission_ThreeSum_LightResidueHistogram
set_option autoImplicit false
open ThreeSum ThreeSum.LightResidueHistogram
open Light Finset ThreeSum.LightResidues ThreeSum.LightHistogram
open ThreeSum.CyclicFold ThreeSum.Karatsuba
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightResidueHistogram.residue_eq_iff {p : ℕ} [NeZero p] (c x : ℤ) {r : ℕ} (hr : r < p) :
    residue p c x = r ↔ ((c * x : ℤ) : ZMod p) = (r : ZMod p) := by sorry
