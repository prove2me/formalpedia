-- Prove2me | Theorems.Thm_QEC_Locality_bkSeparatorRecurrence_eq_zero_of_terminal
-- name    : QEC.Locality.bkSeparatorRecurrence_eq_zero_of_terminal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:12:54.897204+00:00
-- url     : https://prove2.me/theorems/4263c2a1-191d-44f7-9948-a3a9cfc2ff4d
-- title:
--   Locality: bk Separator Recurrence eq zero of terminal
-- statement:
--   The Locality construction uses the bk Separator Recurrence eq zero of terminal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/RecursiveSeparator.lean#L127-L132
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/RecursiveSeparator.lean#L127-L132

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

theorem QEC.Locality.bkSeparatorRecurrence_eq_zero_of_terminal
    (G : ConnectivityGraph ι) (d : Nat) (vertices : Finset ι)
    (hterminal : bkSeparatorTerminal d vertices) :
    bkSeparatorRecurrence G d vertices = 0 := by sorry
