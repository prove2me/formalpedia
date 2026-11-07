-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_0_2_9
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_0_2_9
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:02:57.172636+00:00
-- url     : https://prove2.me/theorems/6f5b8975-6f86-4fad-bf97-58236c186056
-- title:
--   Why24 Appendix ANF: source Coefficient triple 0 2 9
-- statement:
--   The Why24 Appendix ANF construction uses the source Coefficient triple 0 2 9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part01.lean#L40-L42
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part01.lean#L40-L42

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part01
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
set_option maxRecDepth 2048

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_0_2_9 :
    sourceTripleCoefficient 0 2 9 = cubicGateCoefficient 0 2 9 := by sorry
