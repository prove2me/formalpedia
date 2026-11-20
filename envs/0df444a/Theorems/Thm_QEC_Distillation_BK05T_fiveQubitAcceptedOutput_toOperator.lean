-- Prove2me | Theorems.Thm_QEC_Distillation_BK05T_fiveQubitAcceptedOutput_toOperator
-- name    : QEC.Distillation.BK05T.fiveQubitAcceptedOutput_toOperator
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T08:47:34.114075+00:00
-- url     : https://prove2.me/theorems/4c2218e5-eeba-4990-abf2-fe65af6a9fbe
-- title:
--   BK05 T: five Qubit Accepted Output to Operator
-- statement:
--   The BK05 T construction uses the five Qubit Accepted Output to Operator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Postselection.lean#L2610-L2624
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Postselection.lean#L2610-L2624

import Definitions.Def_QECert_BK05T_AcceptedOutput
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK05T
open QEC.Semantics QEC.Semantics.Qubit
open QEC.Distillation.OneQubitMagic
open QEC.Distillation.BK05T.QECertAcceptedOutput
open scoped BigOperators ComplexOrder TensorProduct

theorem QEC.Distillation.BK05T.fiveQubitAcceptedOutput_toOperator
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    (fiveQubitAcceptedOutput epsilon hzero hone).toOperator =
      ((fiveQubitRawTOneCoefficient epsilon /
          fiveQubitSuccessProbability epsilon : Real) : Complex) •
        tZero.toOperator +
      ((fiveQubitRawTZeroCoefficient epsilon /
          fiveQubitSuccessProbability epsilon : Real) : Complex) •
        tOne.toOperator := by sorry
