-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_evaluate_sourcePhasePolynomial
-- name    : QEC.Coding.Why24AppendixANF.evaluate_sourcePhasePolynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:51:53.655202+00:00
-- url     : https://prove2.me/theorems/818de13f-e91d-4503-ac01-57f5dc2c58ca
-- title:
--   Why24 Appendix ANF: evaluate source Phase Polynomial
-- statement:
--   Evaluating the sparse source ANF on any Boolean word gives the actual
--   seventh-power trace of the corresponding selected-basis field element.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Evaluation.lean#L188-L222
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Evaluation.lean#L188-L222

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Field
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Evaluation
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
open scoped BigOperators
open Why24BooleanANF

theorem QEC.Coding.Why24AppendixANF.evaluate_sourcePhasePolynomial (word : Word) :
    evaluate word sourcePhasePolynomial =
      Algebra.trace (ZMod 2) F1024
        ((f1024SelectedCoordinates.symm word) ^ 7) := by sorry
