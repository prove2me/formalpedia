-- Prove2me | Theorems.Thm_QEC_Locality_bkTwoThirdsDepth_mono
-- name    : QEC.Locality.bkTwoThirdsDepth_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:36:37.536867+00:00
-- url     : https://prove2.me/theorems/3800e8c0-99e6-47b7-9e1b-ef21c83c134f
-- title:
--   Locality: bk Two Thirds Depth mono
-- statement:
--   The finite `2/3` depth is monotone in the starting scale.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/SumPreservingRecurrence.lean#L289-L315
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/SumPreservingRecurrence.lean#L289-L315

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_MaxFamily
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_SumPreservingRecurrence
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.bkTwoThirdsDepth_mono
    (d : Nat) {small large : Nat} (hscale : small ≤ large) :
    bkTwoThirdsDepth d small ≤ bkTwoThirdsDepth d large := by sorry
