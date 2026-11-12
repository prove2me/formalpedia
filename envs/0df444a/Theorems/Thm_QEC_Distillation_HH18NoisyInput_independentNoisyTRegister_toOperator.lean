-- Prove2me | Theorems.Thm_QEC_Distillation_HH18NoisyInput_independentNoisyTRegister_toOperator
-- name    : QEC.Distillation.HH18NoisyInput.independentNoisyTRegister_toOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:29:58.756466+00:00
-- url     : https://prove2.me/theorems/7d776426-dcd3-443e-8824-2d2c22bd15f1
-- title:
--   HH18 Noisy Input: independent Noisy TRegister to Operator
-- statement:
--   The HH18 Noisy Input construction uses the independent Noisy TRegister to Operator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/NoisyInput.lean#L288-L295
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/NoisyInput.lean#L288-L295

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PuncturedReedMuller
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_NoisyInput
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18NoisyInput
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open OneQubitMagic
open scoped BigOperators
universe u

theorem QEC.Distillation.HH18NoisyInput.independentNoisyTRegister_toOperator {ι : Type u}
    [Fintype ι] [DecidableEq ι] (epsilon : DiagonalErrorRate) :
    (independentNoisyTRegister (ι := ι) epsilon).toOperator =
      ∑ error : Word (ZMod 2) ι,
        (errorWordWeight epsilon error : Complex) •
          (errorWordDensity error).toOperator := by sorry
