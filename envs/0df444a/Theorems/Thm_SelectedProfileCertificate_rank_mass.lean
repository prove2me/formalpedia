-- Prove2me | Theorems.Thm_SelectedProfileCertificate_rank_mass
-- name    : SelectedProfileCertificate.rank_mass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:10.380199+00:00
-- url     : https://prove2.me/theorems/2badeaa1-b1ed-471a-a9d0-c10c3a38bebb
-- title:
--   SelectedProfileCertificate: Rank mass
-- statement:
--   Exact rational certificate data for the selected PR64 profile. These results retain their stated hypotheses and do not establish the complete fixed-tape multiplication algorithm.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/machine-transfer-verification/next-proof/analytic/SelectedProfileCertificate.lean#L65-L65). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original authorship and assistance credits are retained in the upstream NOTICE and package documentation. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/machine-transfer-verification/next-proof/analytic/SelectedProfileCertificate.lean#L65-L65 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Definitions.Def_AnalyticEnclosures
import Definitions.Def_SelectedProfileCertificate
set_option autoImplicit true
open SelectedProfileCertificate
open AnalyticEnclosures
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem SelectedProfileCertificate.rank_mass : (rows.map (fun r => r.width * r.multiplicity)).sum = 78860441550 := by sorry
