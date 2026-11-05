-- Prove2me | Theorems.Thm_SelectedProfileReal_row_exp_upper
-- name    : SelectedProfileReal.row_exp_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:10.380199+00:00
-- url     : https://prove2.me/theorems/9083231b-d741-464c-9932-fc88692c48b9
-- title:
--   SelectedProfileReal: Row exp upper
-- statement:
--   Real analytic contraction inequalities derived from the selected PR64 rational profile. These results retain their stated hypotheses and do not establish the complete fixed-tape multiplication algorithm.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/machine-transfer-verification/next-proof/analytic/SelectedProfileReal.lean#L41-L49). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original authorship and assistance credits are retained in the upstream NOTICE and package documentation. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/machine-transfer-verification/next-proof/analytic/SelectedProfileReal.lean#L41-L49 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Definitions.Def_SelectedProfileCertificate
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_SelectedProfileReal
set_option autoImplicit true
open SelectedProfileReal
open AnalyticEnclosures SelectedProfileCertificate

theorem SelectedProfileReal.row_exp_upper (r : Row) (hr : r ∈ rows) :
    Real.exp ((saving : ℝ) * Real.log ((m : ℝ) / r.width)) ≤ (r.upper : ℝ) := by sorry
