-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_0_7_8
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_0_7_8
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:43:27.097293+00:00
-- url     : https://prove2.me/theorems/eff117b8-8b47-425c-9caf-d4f01880bee2
-- title:
--   Why24 Appendix ANF: source Coefficient triple 0 7 8
-- statement:
--   The Why24 Appendix ANF construction uses the source Coefficient triple 0 7 8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part04.lean#L48-L50
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part04.lean#L48-L50

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part04
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
set_option maxRecDepth 2048

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_0_7_8 :
    sourceTripleCoefficient 0 7 8 = cubicGateCoefficient 0 7 8 := by sorry
