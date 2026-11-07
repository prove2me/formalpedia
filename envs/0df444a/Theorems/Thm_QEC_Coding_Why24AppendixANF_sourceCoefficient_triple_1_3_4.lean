-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_1_3_4
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_1_3_4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:47:29.095467+00:00
-- url     : https://prove2.me/theorems/9e659f6b-cd9d-4852-95b5-c08452837a08
-- title:
--   Why24 Appendix ANF: source Coefficient triple 1 3 4
-- statement:
--   The Why24 Appendix ANF construction uses the source Coefficient triple 1 3 4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part06.lean#L10-L12
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part06.lean#L10-L12

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part06
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
set_option maxRecDepth 2048

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_1_3_4 :
    sourceTripleCoefficient 1 3 4 = cubicGateCoefficient 1 3 4 := by sorry
