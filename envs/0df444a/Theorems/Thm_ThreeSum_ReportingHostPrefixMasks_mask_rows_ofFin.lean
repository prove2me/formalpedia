-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostPrefixMasks_mask_rows_ofFin
-- name    : ThreeSum.ReportingHostPrefixMasks.mask_rows_ofFin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:54:44.762799+00:00
-- url     : https://prove2.me/theorems/a388e7d2-67c5-4efb-821e-41a6ac18bd98
-- title:
--   Reporting Host Prefix Masks: mask rows of Fin
-- statement:
--   The Reporting Host Prefix Masks construction uses the mask rows of Fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPrefixMasks.lean#L37-L49
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPrefixMasks.lean#L37-L49

import Definitions.Def_Submission_ThreeSum_ReportingHostPairEnumeration
import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Definitions.Def_Submission_ThreeSum_BlockMaskLayout
import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixMasks
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPrefixMasks
open Finset ThreeSum.SubsetAddress BlockRows BlockIndex BlockIndexedQuery BlockMaskLayout
open BlockForced
open ReportingHostPrefixCatalog ReportingHostPairEnumeration
open scoped BigOperators
set_option maxHeartbeats 500000
variable {α : Type*}

theorem ThreeSum.ReportingHostPrefixMasks.mask_rows_ofFin {J L k : ℕ} (hk : k ≤ J) (u : Fin k → Finset (Fin L)) :
    subsetMask (leftPrefix k (fun i : Fin J => if hi : i.val < k then u ⟨i.val,hi⟩ else ∅)) =
      ∑ i : Fin k, 2^(i.val*L)*subsetMask (u i) := by sorry
