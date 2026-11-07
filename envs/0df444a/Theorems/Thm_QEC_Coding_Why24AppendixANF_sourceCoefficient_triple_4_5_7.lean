-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_4_5_7
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_4_5_7
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:08:29.447428+00:00
-- url     : https://prove2.me/theorems/68910d2a-8a78-4d48-b415-627aa0c22a5b
-- title:
--   Why24 Appendix ANF: source Coefficient triple 4 5 7
-- statement:
--   The Why24 Appendix ANF construction uses the source Coefficient triple 4 5 7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part14.lean#L15-L17
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part14.lean#L15-L17

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part14
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
set_option maxRecDepth 2048

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_4_5_7 :
    sourceTripleCoefficient 4 5 7 = cubicGateCoefficient 4 5 7 := by sorry
