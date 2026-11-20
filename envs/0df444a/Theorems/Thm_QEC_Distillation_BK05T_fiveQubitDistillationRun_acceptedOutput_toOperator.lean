-- Prove2me | Theorems.Thm_QEC_Distillation_BK05T_fiveQubitDistillationRun_acceptedOutput_toOperator
-- name    : QEC.Distillation.BK05T.fiveQubitDistillationRun_acceptedOutput_toOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:43:25.731184+00:00
-- url     : https://prove2.me/theorems/6cf7f037-6f9b-4b07-b5e8-dd82d02c6867
-- title:
--   BK05 T: five Qubit Distillation Run accepted Output to Operator
-- statement:
--   The BK05 T construction uses the five Qubit Distillation Run accepted Output to Operator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Postselection.lean#L2626-L2646
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Postselection.lean#L2626-L2646

import Definitions.Def_QEC_Distillation_FiveQubitT_Postselection
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSimpArgs false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK05T
open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open OneQubitMagic
open scoped BigOperators ComplexOrder TensorProduct
attribute [local irreducible] fiveQubitPreparedRowScalar
attribute [local irreducible] GaussianInt.toComplex
attribute [local irreducible] arrayTarget

theorem QEC.Distillation.BK05T.fiveQubitDistillationRun_acceptedOutput_toOperator
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    (fiveQubitDistillationRun epsilon hzero hone).acceptedOutput.toOperator =
      ((fiveQubitSuccessProbability epsilon : Complex)⁻¹) •
        ((fiveQubitRawTOneCoefficient epsilon : Complex) • tZero.toOperator +
          (fiveQubitRawTZeroCoefficient epsilon : Complex) •
            tOne.toOperator) := by sorry
