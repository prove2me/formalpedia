-- Prove2me | Theorems.Thm_ThreeSum_SourceTableLayout_tableAt_of_setAt
-- name    : ThreeSum.SourceTableLayout.tableAt_of_setAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:46:28.011256+00:00
-- url     : https://prove2.me/theorems/ca7fbede-02d8-4928-b8c1-9aa90e40f3a4
-- title:
--   Source Table Layout: table At of set At
-- statement:
--   The Source Table Layout construction uses the table At of set At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceTableLayout.lean#L146-L151
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceTableLayout.lean#L146-L151

import Definitions.Def_Submission_ThreeSum_LightZetaCell
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Mathlib.Data.List.GetD
import Definitions.Def_Submission_ThreeSum_SourceTableLayout
set_option autoImplicit false
open ThreeSum ThreeSum.SourceTableLayout
open SubsetAddress
set_option maxHeartbeats 800000

theorem ThreeSum.SourceTableLayout.tableAt_of_setAt {L cut base : ℕ} {μ : ℕ → ℤ}
    (f : Finset (Fin L) → ℤ)
    (hread : ∀ i < downsetCap L cut, μ (base+i) = f (setAt L cut i)) :
    LightZetaCell.TableAt μ base cut f := by sorry
