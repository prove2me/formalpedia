-- Prove2me | Theorems.Thm_Pr73ProfileCertificate_rational_gap_exact
-- name    : Pr73ProfileCertificate.rational_gap_exact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:10.688206+00:00
-- url     : https://prove2.me/theorems/bf7a98b9-3b2c-4bbc-9fe3-9978a4e30947
-- title:
--   Pr73ProfileCertificate: Rational gap exact
-- statement:
--   Exact rational certificate data for the pinned PR73 profile. These results retain their stated hypotheses and do not establish the complete fixed-tape multiplication algorithm.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/machine-transfer-verification/full-transfer/latest-analytic/Pr73ProfileCertificate.lean#L62-L62). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original authorship and assistance credits are retained in the upstream NOTICE and package documentation. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/machine-transfer-verification/full-transfer/latest-analytic/Pr73ProfileCertificate.lean#L62-L62 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Definitions.Def_AnalyticEnclosures
import Definitions.Def_Pr73ProfileCertificate
set_option autoImplicit true
open Pr73ProfileCertificate
open AnalyticEnclosures
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem Pr73ProfileCertificate.rational_gap_exact : 1 - rationalUpper = (699597017858129667 / 4221114531250000000000000000000000000 : ℚ) := by sorry
