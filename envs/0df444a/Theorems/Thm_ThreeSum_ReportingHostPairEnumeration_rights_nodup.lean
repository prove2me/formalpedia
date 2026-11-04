-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostPairEnumeration_rights_nodup
-- name    : ThreeSum.ReportingHostPairEnumeration.rights_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:44:16.136953+00:00
-- url     : https://prove2.me/theorems/5c8a7a98-f031-4677-86a4-9855ed13ad55
-- title:
--   Reporting Host Pair Enumeration: rights nodup
-- statement:
--   The Reporting Host Pair Enumeration construction uses the rights nodup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPairEnumeration.lean#L68-L69
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPairEnumeration.lean#L68-L69

import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixCatalog
import Definitions.Def_Submission_ThreeSum_QueryCoordinates
import Definitions.Def_Submission_ThreeSum_ReportingHostPairEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPairEnumeration
open Finset ThreeSum.SubsetAddress LayerCounts LocalGraph
set_option linter.unusedSimpArgs false

theorem ThreeSum.ReportingHostPairEnumeration.rights_nodup {L : ℕ} (S : Finset (Fin L)) (h : ℕ) : (rights S h).Nodup := by sorry
