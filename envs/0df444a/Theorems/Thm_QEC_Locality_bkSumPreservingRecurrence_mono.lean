-- Prove2me | Theorems.Thm_QEC_Locality_bkSumPreservingRecurrence_mono
-- name    : QEC.Locality.bkSumPreservingRecurrence_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:15:26.856908+00:00
-- url     : https://prove2.me/theorems/90ee5d46-beb1-40ee-ab03-af1fab1e7359
-- title:
--   Locality: bk Sum Preserving Recurrence mono
-- statement:
--   The source-faithful recurrence is monotone in its parent scale.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/SumPreservingRecurrence.lean#L198-L237
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/SumPreservingRecurrence.lean#L198-L237

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_MaxFamily
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_SumPreservingRecurrence
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.bkSumPreservingRecurrence_mono
    (G : ConnectivityGraph ι) (d : Nat) {small large : Nat} (hscale : small ≤ large) :
    bkSumPreservingRecurrence G d small ≤ bkSumPreservingRecurrence G d large := by sorry
