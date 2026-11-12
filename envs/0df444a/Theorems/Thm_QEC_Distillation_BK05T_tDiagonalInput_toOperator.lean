-- Prove2me | Theorems.Thm_QEC_Distillation_BK05T_tDiagonalInput_toOperator
-- name    : QEC.Distillation.BK05T.tDiagonalInput_toOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:21:25.879205+00:00
-- url     : https://prove2.me/theorems/e28d629b-0c52-4a43-99c2-2c32227752a2
-- title:
--   BK05 T: t Diagonal Input to Operator
-- statement:
--   Its density operator is the sum of the two raw error-word branches.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Input.lean#L107-L112
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Input.lean#L107-L112

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Distillation_FiveQubitT_Input
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK05T
open Semantics Semantics.Qubit
open OneQubitMagic
open scoped BigOperators

theorem QEC.Distillation.BK05T.tDiagonalInput_toOperator (epsilon : Real) (hzero : 0 ≤ epsilon)
    (hone : epsilon ≤ 1) :
    (tDiagonalInput epsilon hzero hone).toOperator =
      ∑ word : Fin 2, tRawInputBranch epsilon word := by sorry
