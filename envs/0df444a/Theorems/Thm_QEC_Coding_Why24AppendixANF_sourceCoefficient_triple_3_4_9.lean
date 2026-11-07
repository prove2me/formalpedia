-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_3_4_9
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_3_4_9
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:02:51.679744+00:00
-- url     : https://prove2.me/theorems/8e7551d1-79e8-4ab5-96f2-8a03a90f8290
-- title:
--   Why24 Appendix ANF: source Coefficient triple 3 4 9
-- statement:
--   The Why24 Appendix ANF construction uses the source Coefficient triple 3 4 9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part12.lean#L30-L32
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part12.lean#L30-L32

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part12
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
set_option maxRecDepth 2048

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_3_4_9 :
    sourceTripleCoefficient 3 4 9 = cubicGateCoefficient 3 4 9 := by sorry
