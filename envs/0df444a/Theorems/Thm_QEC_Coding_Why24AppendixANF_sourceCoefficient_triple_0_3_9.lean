-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_0_3_9
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_0_3_9
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:39:57.143689+00:00
-- url     : https://prove2.me/theorems/a4325c33-577f-446d-98de-e9d699b1c398
-- title:
--   Why24 Appendix ANF: source Coefficient triple 0 3 9
-- statement:
--   The Why24 Appendix ANF construction uses the source Coefficient triple 0 3 9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part02.lean#L35-L37
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part02.lean#L35-L37

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part02
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
set_option maxRecDepth 2048

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_0_3_9 :
    sourceTripleCoefficient 0 3 9 = cubicGateCoefficient 0 3 9 := by sorry
