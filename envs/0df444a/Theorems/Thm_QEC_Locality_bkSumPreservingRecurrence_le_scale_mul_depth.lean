-- Prove2me | Theorems.Thm_QEC_Locality_bkSumPreservingRecurrence_le_scale_mul_depth
-- name    : QEC.Locality.bkSumPreservingRecurrence_le_scale_mul_depth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:36:58.818994+00:00
-- url     : https://prove2.me/theorems/a6c9b3c3-d7a6-479a-9193-7d2aa07886b3
-- title:
--   Locality: bk Sum Preserving Recurrence le scale mul depth
-- statement:
--   Every measured graph profile gives the universal finite logarithmic-depth bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/SumPreservingRecurrence.lean#L396-L402
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/SumPreservingRecurrence.lean#L396-L402

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_MaxFamily
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_SumPreservingRecurrence
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.bkSumPreservingRecurrence_le_scale_mul_depth
    (G : ConnectivityGraph ι) (d parent : Nat) :
    bkSumPreservingRecurrence G d parent ≤ parent * bkTwoThirdsDepth d parent := by sorry
