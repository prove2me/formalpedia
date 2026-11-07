-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_0_1_4
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_0_1_4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:36:47.448479+00:00
-- url     : https://prove2.me/theorems/f6a01a72-5c35-4f64-b9af-a509598bc433
-- title:
--   Why24 Appendix ANF: source Coefficient triple 0 1 4
-- statement:
--   The Why24 Appendix ANF construction uses the source Coefficient triple 0 1 4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part00.lean#L20-L22
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part00.lean#L20-L22

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Probe
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part00
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
set_option maxRecDepth 2048

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_0_1_4 :
    sourceTripleCoefficient 0 1 4 = cubicGateCoefficient 0 1 4 := by sorry
