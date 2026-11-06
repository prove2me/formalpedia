-- Prove2me | Theorems.Thm_QEC_Locality_bkTwoThirdsDepth_eq_succ
-- name    : QEC.Locality.bkTwoThirdsDepth_eq_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:15:35.559633+00:00
-- url     : https://prove2.me/theorems/1142c359-51d8-4a89-a685-720ef8ab3962
-- title:
--   Locality: bk Two Thirds Depth eq succ
-- statement:
--   The Locality construction uses the bk Two Thirds Depth eq succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/SumPreservingRecurrence.lean#L281-L286
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/SumPreservingRecurrence.lean#L281-L286

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_MaxFamily
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_SumPreservingRecurrence
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.bkTwoThirdsDepth_eq_succ
    (d parent : Nat) (hterminal : ¬bkScaleTerminal d parent) :
    bkTwoThirdsDepth d parent =
      1 + bkTwoThirdsDepth d (bkTwoThirdsChildScale parent) := by sorry
