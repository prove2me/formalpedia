-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_3_4_6
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_3_4_6
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:02:35.998567+00:00
-- url     : https://prove2.me/theorems/83839dca-ca54-4e3a-8a24-100f51151f9a
-- title:
--   Why24 Appendix ANF: source Coefficient triple 3 4 6
-- statement:
--   The Why24 Appendix ANF construction uses the source Coefficient triple 3 4 6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part12.lean#L15-L17
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part12.lean#L15-L17

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part12
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
set_option maxRecDepth 2048

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_3_4_6 :
    sourceTripleCoefficient 3 4 6 = cubicGateCoefficient 3 4 6 := by sorry
