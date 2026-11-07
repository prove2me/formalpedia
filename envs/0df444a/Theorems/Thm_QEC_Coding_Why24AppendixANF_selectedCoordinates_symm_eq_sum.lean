-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_selectedCoordinates_symm_eq_sum
-- name    : QEC.Coding.Why24AppendixANF.selectedCoordinates_symm_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:43:11.701105+00:00
-- url     : https://prove2.me/theorems/a2114898-e197-43a7-8e13-00fbbbb73782
-- title:
--   Why24 Appendix ANF: selected Coordinates symm eq sum
-- statement:
--   The Why24 Appendix ANF construction uses the selected Coordinates symm eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Evaluation.lean#L45-L49
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Evaluation.lean#L45-L49

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Field
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Evaluation
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
open scoped BigOperators
open Why24BooleanANF

theorem QEC.Coding.Why24AppendixANF.selectedCoordinates_symm_eq_sum (word : Word) :
    f1024SelectedCoordinates.symm word =
      ∑ selected : Fin 10,
        word selected • f1024SelectedSelfDualBasis selected := by sorry
