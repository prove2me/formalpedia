-- Prove2me | Theorems.Thm_QEC_Locality_bkScaleRecurrence_eq_zero_of_terminal
-- name    : QEC.Locality.bkScaleRecurrence_eq_zero_of_terminal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:33:48.230664+00:00
-- url     : https://prove2.me/theorems/c52c8e8f-4c02-479b-913f-a0ec74e85f0e
-- title:
--   Locality: bk Scale Recurrence eq zero of terminal
-- statement:
--   The Locality construction uses the bk Scale Recurrence eq zero of terminal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/RecursiveSeparator.lean#L186-L190
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/RecursiveSeparator.lean#L186-L190

import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Definitions.Def_QEC_Locality_CorrectableRegions_SemanticDistanceErasure
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.bkScaleRecurrence_eq_zero_of_terminal
    (G : ConnectivityGraph ι) (d r : Nat) (hterminal : bkScaleTerminal d r) :
    bkScaleRecurrence G d r = 0 := by sorry
