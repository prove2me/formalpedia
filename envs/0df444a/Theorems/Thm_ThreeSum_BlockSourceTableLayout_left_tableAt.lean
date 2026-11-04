-- Prove2me | Theorems.Thm_ThreeSum_BlockSourceTableLayout_left_tableAt
-- name    : ThreeSum.BlockSourceTableLayout.left_tableAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:05:39.314925+00:00
-- url     : https://prove2.me/theorems/4e5f7939-f3f6-4ef7-bd32-889d28734e36
-- title:
--   Block Source Table Layout: left table At
-- statement:
--   The Block Source Table Layout construction uses the left table At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceTableLayout.lean#L22-L29
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceTableLayout.lean#L22-L29

import Definitions.Def_Submission_ThreeSum_SourceTableLayout
import Definitions.Def_Submission_ThreeSum_BlockIndexedQuery
import Definitions.Def_Submission_ThreeSum_BlockSourceTableLayout
set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceTableLayout
open SubsetAddress BlockIndex BlockEncoding BlockRows GlobalEncoding

theorem ThreeSum.BlockSourceTableLayout.left_tableAt {β : Type*} [Fintype β] [DecidableEq β]
    {h J cut base : ℕ} {μ : ℕ → ℤ}
    (P : ℤ) (B : Finset β) (b : β → ℤ) (q : GlobalOutput h J)
    (hread : ∀ i < downsetCap (J*(512*h)) cut,
      μ (base+i) = (leftWeights (outputOccurrences q) P B b (sets h J cut i) : ℤ)) :
    LightZetaCell.TableAt μ base cut (BlockIndexedQuery.leftSource P B b q) := by sorry
