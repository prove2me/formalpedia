-- Prove2me | Theorems.Thm_ThreeSum_Bands_overlap_card_le
-- name    : ThreeSum.Bands.overlap_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:00:33.667002+00:00
-- url     : https://prove2.me/theorems/f6de3133-5cad-46de-9233-9d9d6378cdcd
-- title:
--   Bands: overlap card le
-- statement:
--   The Bands construction uses the overlap card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Bands.lean#L80-L90
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Bands.lean#L80-L90

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sets
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_Bands
set_option autoImplicit false
open ThreeSum ThreeSum.Bands
variable {I J K : Type*}

theorem ThreeSum.Bands.overlap_card_le [Fintype I] [Fintype J]
    {alo ahi : I → ℤ} {blo bhi : J → ℤ}
    (hA : Separated alo ahi) (hB : Separated blo bhi) :
    Fintype.card {p : I × J // Overlap alo ahi blo bhi p} ≤
      Fintype.card I + Fintype.card J := by sorry
