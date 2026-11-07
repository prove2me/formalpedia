-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_2_3_6
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_2_3_6
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:54:41.605084+00:00
-- url     : https://prove2.me/theorems/b16ba52e-076a-44e3-9fdb-a6b466e42c1c
-- title:
--   Why24 Appendix ANF: source Coefficient triple 2 3 6
-- statement:
--   The Why24 Appendix ANF construction uses the source Coefficient triple 2 3 6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part09.lean#L20-L22
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part09.lean#L20-L22

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part09
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
set_option maxRecDepth 2048

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_2_3_6 :
    sourceTripleCoefficient 2 3 6 = cubicGateCoefficient 2 3 6 := by sorry
