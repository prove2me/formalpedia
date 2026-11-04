-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostPairEnumeration_lefts_nodup
-- name    : ThreeSum.ReportingHostPairEnumeration.lefts_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:44:27.905384+00:00
-- url     : https://prove2.me/theorems/ceb4c5a2-de72-4a56-bbb3-e839cc8bc6f1
-- title:
--   Reporting Host Pair Enumeration: lefts nodup
-- statement:
--   The Reporting Host Pair Enumeration construction uses the lefts nodup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPairEnumeration.lean#L36-L42
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPairEnumeration.lean#L36-L42

import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixCatalog
import Definitions.Def_Submission_ThreeSum_QueryCoordinates
import Definitions.Def_Submission_ThreeSum_ReportingHostPairEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPairEnumeration
open Finset ThreeSum.SubsetAddress LayerCounts LocalGraph
set_option linter.unusedSimpArgs false

theorem ThreeSum.ReportingHostPairEnumeration.lefts_nodup (L h : ℕ) : (lefts L h).Nodup := by sorry
