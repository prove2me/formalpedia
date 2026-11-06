-- Prove2me | Theorems.Thm_QEC_Locality_bkSumPreservingRecurrence_eq_zero_of_terminal
-- name    : QEC.Locality.bkSumPreservingRecurrence_eq_zero_of_terminal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:07:27.636404+00:00
-- url     : https://prove2.me/theorems/4dae384d-58a4-4a59-abad-5c0fb8f45f60
-- title:
--   Locality: bk Sum Preserving Recurrence eq zero of terminal
-- statement:
--   The Locality construction uses the bk Sum Preserving Recurrence eq zero of terminal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/SumPreservingRecurrence.lean#L70-L75
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/SumPreservingRecurrence.lean#L70-L75

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_MaxFamily
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_SumPreservingRecurrence
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.bkSumPreservingRecurrence_eq_zero_of_terminal
    (G : ConnectivityGraph ι) (d parent : Nat)
    (hterminal : bkScaleTerminal d parent) :
    bkSumPreservingRecurrence G d parent = 0 := by sorry
