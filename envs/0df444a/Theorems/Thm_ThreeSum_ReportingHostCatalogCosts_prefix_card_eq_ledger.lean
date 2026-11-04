-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostCatalogCosts_prefix_card_eq_ledger
-- name    : ThreeSum.ReportingHostCatalogCosts.prefix_card_eq_ledger
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:45:51.143314+00:00
-- url     : https://prove2.me/theorems/0a42b2ab-763b-4efc-9792-50606facb5ce
-- title:
--   Reporting Host Catalog Costs: prefix card eq ledger
-- statement:
--   The Reporting Host Catalog Costs construction uses the prefix card eq ledger property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostCatalogCosts.lean#L58-L63
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostCatalogCosts.lean#L58-L63

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

theorem ThreeSum.ReportingHostCatalogCosts.prefix_card_eq_ledger {n h k : ℕ} (hsize : 2*h = Scales.muZero n) :
    Fintype.card (Prefix h k) = CostLedger.prefixChoices n k := by sorry
