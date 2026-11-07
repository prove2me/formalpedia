-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_1_4_6
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_1_4_6
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:52:33.300323+00:00
-- url     : https://prove2.me/theorems/440a0b4b-bcf7-4516-9695-536308106fd7
-- title:
--   Why24 Appendix ANF: source Coefficient triple 1 4 6
-- statement:
--   The Why24 Appendix ANF construction uses the source Coefficient triple 1 4 6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part07.lean#L15-L17
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part07.lean#L15-L17

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part07
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
set_option maxRecDepth 2048

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_1_4_6 :
    sourceTripleCoefficient 1 4 6 = cubicGateCoefficient 1 4 6 := by sorry
