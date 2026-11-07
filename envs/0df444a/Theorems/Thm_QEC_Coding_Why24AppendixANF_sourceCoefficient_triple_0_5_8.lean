-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_0_5_8
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_0_5_8
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:44:19.055592+00:00
-- url     : https://prove2.me/theorems/c9f26657-2b8b-4fb2-bb9c-93d29f300f4b
-- title:
--   Why24 Appendix ANF: source Coefficient triple 0 5 8
-- statement:
--   The Why24 Appendix ANF construction uses the source Coefficient triple 0 5 8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part03.lean#L66-L68
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part03.lean#L66-L68

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part03
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
set_option maxRecDepth 2048

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_0_5_8 :
    sourceTripleCoefficient 0 5 8 = cubicGateCoefficient 0 5 8 := by sorry
