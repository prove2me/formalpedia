-- Prove2me | Theorems.Thm_ThreeSum_LightResidueHistogram_residue_zmod
-- name    : ThreeSum.LightResidueHistogram.residue_zmod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:28:55.020585+00:00
-- url     : https://prove2.me/theorems/12722203-da0e-4d02-a565-8370b9f62a22
-- title:
--   Light Residue Histogram: residue zmod
-- statement:
--   The Light Residue Histogram construction uses the residue zmod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightResidueHistogram.lean#L40-L44
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightResidueHistogram.lean#L40-L44

import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_LightHistogram
import Definitions.Def_Submission_ThreeSum_CyclicFold
import Definitions.Def_Submission_ThreeSum_LightResidueHistogram
set_option autoImplicit false
open ThreeSum ThreeSum.LightResidueHistogram
open Light Finset ThreeSum.LightResidues ThreeSum.LightHistogram
open ThreeSum.CyclicFold ThreeSum.Karatsuba
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightResidueHistogram.residue_zmod {p : ℕ} (hp : 0 < p) (c x : ℤ) :
    (residue p c x : ZMod p) = ((c * x : ℤ) : ZMod p) := by sorry
