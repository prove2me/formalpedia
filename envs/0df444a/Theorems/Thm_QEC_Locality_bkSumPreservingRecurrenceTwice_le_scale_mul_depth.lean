-- Prove2me | Theorems.Thm_QEC_Locality_bkSumPreservingRecurrenceTwice_le_scale_mul_depth
-- name    : QEC.Locality.bkSumPreservingRecurrenceTwice_le_scale_mul_depth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:26:39.140453+00:00
-- url     : https://prove2.me/theorems/df0b42ed-2e7d-442c-a7c5-e1b7f3e05609
-- title:
--   Locality: bk Sum Preserving Recurrence Twice le scale mul depth
-- statement:
--   The exact two-pass composition has a fully finite second-pass estimate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/SumPreservingRecurrence.lean#L405-L411
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/SumPreservingRecurrence.lean#L405-L411

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_MaxFamily
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_SumPreservingRecurrence
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.bkSumPreservingRecurrenceTwice_le_scale_mul_depth
    (G : ConnectivityGraph ι) (d parent : Nat) :
    bkSumPreservingRecurrenceTwice G d parent ≤
      bkSumPreservingRecurrence G d parent *
        bkTwoThirdsDepth d (bkSumPreservingRecurrence G d parent) := by sorry
