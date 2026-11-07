-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_3_4_5
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_3_4_5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:02:31.513191+00:00
-- url     : https://prove2.me/theorems/83199dee-f040-4ac3-b0b0-c35b6ae3251c
-- title:
--   Why24 Appendix ANF: source Coefficient triple 3 4 5
-- statement:
--   The Why24 Appendix ANF construction uses the source Coefficient triple 3 4 5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part12.lean#L10-L12
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part12.lean#L10-L12

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part12
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
set_option maxRecDepth 2048

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_3_4_5 :
    sourceTripleCoefficient 3 4 5 = cubicGateCoefficient 3 4 5 := by sorry
