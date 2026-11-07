-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_0_8_9
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_0_8_9
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:43:38.727993+00:00
-- url     : https://prove2.me/theorems/d62ad753-f2c6-45d6-8046-e9ee3a83e3f3
-- title:
--   Why24 Appendix ANF: source Coefficient triple 0 8 9
-- statement:
--   The Why24 Appendix ANF construction uses the source Coefficient triple 0 8 9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part04.lean#L82-L84
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part04.lean#L82-L84

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part04
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
set_option maxRecDepth 2048

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_0_8_9 :
    sourceTripleCoefficient 0 8 9 = cubicGateCoefficient 0 8 9 := by sorry
