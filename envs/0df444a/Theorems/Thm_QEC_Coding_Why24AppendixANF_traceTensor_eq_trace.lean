-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_traceTensor_eq_trace
-- name    : QEC.Coding.Why24AppendixANF.traceTensor_eq_trace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:51:25.67019+00:00
-- url     : https://prove2.me/theorems/3ef56e88-68a3-4614-8f94-dc5162352518
-- title:
--   Why24 Appendix ANF: trace Tensor eq trace
-- statement:
--   The Why24 Appendix ANF construction uses the trace Tensor eq trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Evaluation.lean#L129-L149
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Evaluation.lean#L129-L149

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Field
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Evaluation
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
open scoped BigOperators
open Why24BooleanANF

theorem QEC.Coding.Why24AppendixANF.traceTensor_eq_trace (first second third : Fin 10) :
    traceTensor first second third =
      Algebra.trace (ZMod 2) F1024
        (f1024SelectedSelfDualBasis first *
          f1024SelectedSelfDualBasis second ^ 2 *
          f1024SelectedSelfDualBasis third ^ 4) := by sorry
