-- Prove2me | Theorems.Thm_ThreeSum_Bands_separated_shift
-- name    : ThreeSum.Bands.separated_shift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:10:54.972796+00:00
-- url     : https://prove2.me/theorems/cf824219-6013-49fb-8f9b-148a1269a593
-- title:
--   Bands: separated shift
-- statement:
--   The Bands construction uses the separated shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Bands.lean#L34-L40
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Bands.lean#L34-L40

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

theorem ThreeSum.Bands.separated_shift {lo hi : I → ℤ} (hs : Separated lo hi) (t : ℤ) :
    Separated (fun i => t + lo i) (fun i => t + hi i) := by sorry
