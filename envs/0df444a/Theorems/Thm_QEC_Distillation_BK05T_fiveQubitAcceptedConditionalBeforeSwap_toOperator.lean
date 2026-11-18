-- Prove2me | Theorems.Thm_QEC_Distillation_BK05T_fiveQubitAcceptedConditionalBeforeSwap_toOperator
-- name    : QEC.Distillation.BK05T.fiveQubitAcceptedConditionalBeforeSwap_toOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-17T19:21:14.085424+00:00
-- url     : https://prove2.me/theorems/9668eefb-0f8e-4430-9337-3cf5699ef894
-- title:
--   BK05 T: five Qubit Accepted Conditional Before Swap to Operator
-- statement:
--   The BK05 T construction uses the five Qubit Accepted Conditional Before Swap to Operator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Postselection.lean#L2433-L2446
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Postselection.lean#L2433-L2446

import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Distillation_FiveQubitT_Input
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
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

theorem QEC.Distillation.BK05T.fiveQubitAcceptedConditionalBeforeSwap_toOperator
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    (fiveQubitAcceptedConditionalBeforeSwap epsilon hzero hone).toOperator =
      ((fiveQubitSuccessProbability epsilon : Complex)⁻¹) •
        ((fiveQubitRawTZeroCoefficient epsilon : Complex) • tZero.toOperator +
          (fiveQubitRawTOneCoefficient epsilon : Complex) •
            tOne.toOperator) := by sorry
