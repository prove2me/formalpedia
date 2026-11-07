-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_0_2_5
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_0_2_5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:01:54.355745+00:00
-- url     : https://prove2.me/theorems/44b7152b-ad19-484e-b2d1-aa80dfc850be
-- title:
--   Why24 Appendix ANF: source Coefficient triple 0 2 5
-- statement:
--   The Why24 Appendix ANF construction uses the source Coefficient triple 0 2 5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part01.lean#L20-L22
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part01.lean#L20-L22

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part01
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
set_option maxRecDepth 2048

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_0_2_5 :
    sourceTripleCoefficient 0 2 5 = cubicGateCoefficient 0 2 5 := by sorry
