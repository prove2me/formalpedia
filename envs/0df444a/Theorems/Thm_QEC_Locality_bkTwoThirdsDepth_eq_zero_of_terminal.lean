-- Prove2me | Theorems.Thm_QEC_Locality_bkTwoThirdsDepth_eq_zero_of_terminal
-- name    : QEC.Locality.bkTwoThirdsDepth_eq_zero_of_terminal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:36:51.00071+00:00
-- url     : https://prove2.me/theorems/22b39b6f-a709-4d1e-8ae7-c871ad4b33e1
-- title:
--   Locality: bk Two Thirds Depth eq zero of terminal
-- statement:
--   The Locality construction uses the bk Two Thirds Depth eq zero of terminal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/SumPreservingRecurrence.lean#L275-L279
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/SumPreservingRecurrence.lean#L275-L279

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_MaxFamily
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_SumPreservingRecurrence
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.bkTwoThirdsDepth_eq_zero_of_terminal
    (d parent : Nat) (hterminal : bkScaleTerminal d parent) :
    bkTwoThirdsDepth d parent = 0 := by sorry
