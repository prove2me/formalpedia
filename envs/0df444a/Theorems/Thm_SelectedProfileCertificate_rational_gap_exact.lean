-- Prove2me | Theorems.Thm_SelectedProfileCertificate_rational_gap_exact
-- name    : SelectedProfileCertificate.rational_gap_exact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:10.380199+00:00
-- url     : https://prove2.me/theorems/fe305026-d6ec-444b-9142-14c05b21433b
-- title:
--   SelectedProfileCertificate: Rational gap exact
-- statement:
--   Exact rational certificate data for the selected PR64 profile. These results retain their stated hypotheses and do not establish the complete fixed-tape multiplication algorithm.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/machine-transfer-verification/next-proof/analytic/SelectedProfileCertificate.lean#L63-L63). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original authorship and assistance credits are retained in the upstream NOTICE and package documentation. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/machine-transfer-verification/next-proof/analytic/SelectedProfileCertificate.lean#L63-L63 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Definitions.Def_AnalyticEnclosures
import Definitions.Def_SelectedProfileCertificate
set_option autoImplicit true
open SelectedProfileCertificate
open AnalyticEnclosures
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem SelectedProfileCertificate.rational_gap_exact : 1 - rationalUpper = (23551960513937 / 4285993937500000000000000000000000000 : ℚ) := by sorry
