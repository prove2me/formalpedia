-- Prove2me | Theorems.Thm_SelectedProfileCertificate_logTwo_certificate
-- name    : SelectedProfileCertificate.logTwo_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:10.380199+00:00
-- url     : https://prove2.me/theorems/433f9a9a-8af3-4511-b415-d702f921cfaa
-- title:
--   SelectedProfileCertificate: Log Two certificate
-- statement:
--   Exact rational certificate data for the selected PR64 profile. These results retain their stated hypotheses and do not establish the complete fixed-tape multiplication algorithm.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/machine-transfer-verification/next-proof/analytic/SelectedProfileCertificate.lean#L60-L60). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original authorship and assistance credits are retained in the upstream NOTICE and package documentation. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/machine-transfer-verification/next-proof/analytic/SelectedProfileCertificate.lean#L60-L60 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Definitions.Def_AnalyticEnclosures
import Definitions.Def_SelectedProfileCertificate
set_option autoImplicit true
open SelectedProfileCertificate
open AnalyticEnclosures
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem SelectedProfileCertificate.logTwo_certificate : 0 ≤ logTwoUpper ∧ (2 : ℚ) ≤ expPoly logTwoUpper 24 := by sorry
