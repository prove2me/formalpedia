-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostCatalogCosts_prefix_card_pos
-- name    : ThreeSum.ReportingHostCatalogCosts.prefix_card_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:45:55.416209+00:00
-- url     : https://prove2.me/theorems/fb4e20cc-77fb-4093-a9d6-1b5dbf0aa734
-- title:
--   Reporting Host Catalog Costs: prefix card pos
-- statement:
--   The Reporting Host Catalog Costs construction uses the prefix card pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostCatalogCosts.lean#L21-L23
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostCatalogCosts.lean#L21-L23

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixCatalogSetup
import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixCatalog
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffixCosts
import Definitions.Def_Submission_ThreeSum_CostLedger
import Definitions.Def_Submission_ThreeSum_ReportingHostCatalogCosts
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostCatalogCosts
set_option maxRecDepth 8000
open ThreeSum.SubsetAddress ThreeSum.LightBlockQuery ThreeSum.BlockIndexedQuery
open ReportingHostPrefixCatalog ReportingHostSuffixCosts

theorem ThreeSum.ReportingHostCatalogCosts.prefix_card_pos (h k : ℕ) : 0 < Fintype.card (Prefix h k) := by sorry
