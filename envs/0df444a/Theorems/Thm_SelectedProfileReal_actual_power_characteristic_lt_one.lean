-- Prove2me | Theorems.Thm_SelectedProfileReal_actual_power_characteristic_lt_one
-- name    : SelectedProfileReal.actual_power_characteristic_lt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:10.380199+00:00
-- url     : https://prove2.me/theorems/71a65d32-be7d-4bbe-b299-603c7740f9d2
-- title:
--   SelectedProfileReal: Actual power characteristic lt one
-- statement:
--   Kernel theorem: the literal selected profile has actual real contraction at a=63787735011827529/1250000000000000000000. No enclosure premise remains.
--
--   Real analytic contraction inequalities derived from the selected PR64 rational profile. These results retain their stated hypotheses and do not establish the complete fixed-tape multiplication algorithm.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/machine-transfer-verification/next-proof/analytic/SelectedProfileReal.lean#L94-L103). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original authorship and assistance credits are retained in the upstream NOTICE and package documentation. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/machine-transfer-verification/next-proof/analytic/SelectedProfileReal.lean#L94-L103 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Definitions.Def_SelectedProfileCertificate
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_SelectedProfileReal
set_option autoImplicit true
open SelectedProfileReal
open AnalyticEnclosures SelectedProfileCertificate

theorem SelectedProfileReal.actual_power_characteristic_lt_one : powerCharacteristic < 1 := by sorry
