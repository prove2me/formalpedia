-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_1_2_5
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_1_2_5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:47:13.865588+00:00
-- url     : https://prove2.me/theorems/19aa1556-a162-4b73-9bff-9f279300faf7
-- title:
--   Why24 Appendix ANF: source Coefficient triple 1 2 5
-- statement:
--   The Why24 Appendix ANF construction uses the source Coefficient triple 1 2 5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part05.lean#L20-L22
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part05.lean#L20-L22

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part05
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
set_option maxRecDepth 2048

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_1_2_5 :
    sourceTripleCoefficient 1 2 5 = cubicGateCoefficient 1 2 5 := by sorry
