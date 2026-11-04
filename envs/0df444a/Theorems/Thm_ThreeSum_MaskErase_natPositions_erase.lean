-- Prove2me | Theorems.Thm_ThreeSum_MaskErase_natPositions_erase
-- name    : ThreeSum.MaskErase.natPositions_erase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:05:01.570265+00:00
-- url     : https://prove2.me/theorems/643c3b25-46dc-4f9b-9d07-80ce078a71a0
-- title:
--   Mask Erase: nat Positions erase
-- statement:
--   The Mask Erase construction uses the nat Positions erase property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/MaskErase.lean#L76-L78
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/MaskErase.lean#L76-L78

import Definitions.Def_Submission_ThreeSum_SubsetAddress
import Definitions.Def_Submission_ThreeSum_MaskErase
set_option autoImplicit false
open ThreeSum ThreeSum.MaskErase
open Finset
open scoped BigOperators
open SubsetAddress

theorem ThreeSum.MaskErase.natPositions_erase {L : ℕ} (s : Finset (Fin L)) (a : Fin L) :
    natPositions (s.erase a) = (natPositions s).erase a.val := by sorry
