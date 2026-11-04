-- Prove2me | Theorems.Thm_ThreeSum_BlockSourceTableLayout_right_tableAt
-- name    : ThreeSum.BlockSourceTableLayout.right_tableAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:05:41.94166+00:00
-- url     : https://prove2.me/theorems/67213885-feb3-4ad1-b611-3c7136c60f52
-- title:
--   Block Source Table Layout: right table At
-- statement:
--   The Block Source Table Layout construction uses the right table At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceTableLayout.lean#L31-L38
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceTableLayout.lean#L31-L38

import Definitions.Def_Submission_ThreeSum_SourceTableLayout
import Definitions.Def_Submission_ThreeSum_BlockIndexedQuery
import Definitions.Def_Submission_ThreeSum_BlockSourceTableLayout
set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceTableLayout
open SubsetAddress BlockIndex BlockEncoding BlockRows GlobalEncoding

theorem ThreeSum.BlockSourceTableLayout.right_tableAt {β : Type*} [Fintype β] [DecidableEq β]
    {h J cut base : ℕ} {μ : ℕ → ℤ}
    (P shift : ℤ) (C : Finset β) (c : β → ℤ) (q : GlobalOutput h J)
    (hread : ∀ i < downsetCap (J*(512*h)) cut,
      μ (base+i) = (rightWeights (outputOccurrences q) P shift C c (sets h J cut i) : ℤ)) :
    LightZetaCell.TableAt μ base cut (BlockIndexedQuery.rightSource P shift C c q) := by sorry
