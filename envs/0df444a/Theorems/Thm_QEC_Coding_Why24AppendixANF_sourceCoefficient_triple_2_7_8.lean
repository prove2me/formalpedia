-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_2_7_8
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_2_7_8
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:05:26.237228+00:00
-- url     : https://prove2.me/theorems/c0883ed2-4e42-401a-a1e3-708c8c38b491
-- title:
--   Why24 Appendix ANF: source Coefficient triple 2 7 8
-- statement:
--   The Why24 Appendix ANF construction uses the source Coefficient triple 2 7 8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part11.lean#L48-L50
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part11.lean#L48-L50

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part11
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
set_option maxRecDepth 2048

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_2_7_8 :
    sourceTripleCoefficient 2 7 8 = cubicGateCoefficient 2 7 8 := by sorry
