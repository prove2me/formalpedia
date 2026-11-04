-- Prove2me | Theorems.Thm_ThreeSum_OneHotMask_mem_natPositions
-- name    : ThreeSum.OneHotMask.mem_natPositions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:15:38.810647+00:00
-- url     : https://prove2.me/theorems/568ba476-a27f-472b-8d86-fb0273e1b0e5
-- title:
--   One Hot Mask: mem nat Positions
-- statement:
--   The One Hot Mask construction uses the mem nat Positions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OneHotMask.lean#L79-L87
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OneHotMask.lean#L79-L87

import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Definitions.Def_Submission_ThreeSum_MaskErase
import Definitions.Def_Submission_ThreeSum_OneHotMask
set_option autoImplicit false
open ThreeSum ThreeSum.OneHotMask
open Finset SubsetAddress LocalHashMoments
open scoped BigOperators
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

theorem ThreeSum.OneHotMask.mem_natPositions {L : ℕ} (s : Finset (Fin L)) (i : Fin L) :
    i.val ∈ natPositions s ↔ i ∈ s := by sorry
