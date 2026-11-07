-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_1_4_7
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_1_4_7
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:52:32.238072+00:00
-- url     : https://prove2.me/theorems/dbc1a671-81d8-431d-827d-383240fcbf5e
-- title:
--   Why24 Appendix ANF: source Coefficient triple 1 4 7
-- statement:
--   The Why24 Appendix ANF construction uses the source Coefficient triple 1 4 7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part07.lean#L20-L22
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part07.lean#L20-L22

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part07
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
set_option maxRecDepth 2048

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_1_4_7 :
    sourceTripleCoefficient 1 4 7 = cubicGateCoefficient 1 4 7 := by sorry
