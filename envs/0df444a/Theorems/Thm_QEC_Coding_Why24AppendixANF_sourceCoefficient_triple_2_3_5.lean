-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_2_3_5
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_2_3_5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:54:43.862266+00:00
-- url     : https://prove2.me/theorems/af04f1bb-0561-46e8-9d0d-7b7a9fe3497e
-- title:
--   Why24 Appendix ANF: source Coefficient triple 2 3 5
-- statement:
--   The Why24 Appendix ANF construction uses the source Coefficient triple 2 3 5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part09.lean#L15-L17
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part09.lean#L15-L17

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part09
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
set_option maxRecDepth 2048

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_2_3_5 :
    sourceTripleCoefficient 2 3 5 = cubicGateCoefficient 2 3 5 := by sorry
