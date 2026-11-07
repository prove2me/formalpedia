-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_1_8_9
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_1_8_9
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:51:48.309679+00:00
-- url     : https://prove2.me/theorems/a1438a4f-1ad0-4880-b064-79635b699262
-- title:
--   Why24 Appendix ANF: source Coefficient triple 1 8 9
-- statement:
--   The Why24 Appendix ANF construction uses the source Coefficient triple 1 8 9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part08.lean#L82-L84
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part08.lean#L82-L84

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part08
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
set_option maxRecDepth 2048

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_1_8_9 :
    sourceTripleCoefficient 1 8 9 = cubicGateCoefficient 1 8 9 := by sorry
