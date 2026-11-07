-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_2_5_6
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_2_5_6
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:04:13.184109+00:00
-- url     : https://prove2.me/theorems/a0fc7ab8-2c5f-41c9-a739-4843b1402d69
-- title:
--   Why24 Appendix ANF: source Coefficient triple 2 5 6
-- statement:
--   The Why24 Appendix ANF construction uses the source Coefficient triple 2 5 6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part10.lean#L56-L58
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part10.lean#L56-L58

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part10
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
set_option maxRecDepth 2048

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_2_5_6 :
    sourceTripleCoefficient 2 5 6 = cubicGateCoefficient 2 5 6 := by sorry
