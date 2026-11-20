-- Prove2me | Theorems.Thm_QEC_Distillation_BK05T_bk05TIteration_eventually_lt_of_tFidelity
-- name    : QEC.Distillation.BK05T.bk05TIteration_eventually_lt_of_tFidelity
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T07:42:34.165376+00:00
-- url     : https://prove2.me/theorems/c86d1552-fb24-4f88-b253-2636e9fec535
-- title:
--   BK05 T: bk05 TIteration eventually lt of t Fidelity
-- statement:
--   The same exact square-root fidelity premise gives a finite accepted-round
--   witness for every positive target error.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Recurrence.lean#L661-L669
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Recurrence.lean#L661-L669

import Definitions.Def_QEC_Distillation_FiveQubitT_Postselection
import Definitions.Def_QEC_Distillation_FiveQubitT_Recurrence
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK05T
open Semantics Semantics.Qubit
open OneQubitMagic

theorem QEC.Distillation.BK05T.bk05TIteration_eventually_lt_of_tFidelity
    (rho : DensityOperator QubitSpace)
    (hfidelity : bk05TFidelityThreshold < tFidelity rho)
    (target : Real) (htarget : 0 < target) :
    ∃ rounds : Nat,
      bk05TIteration (bk05TFidelityError rho) rounds < target := by sorry
