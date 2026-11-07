-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_1_3_9
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_1_3_9
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:47:41.629564+00:00
-- url     : https://prove2.me/theorems/7c2feabd-83ad-43fc-ba3d-86f19d7a1018
-- title:
--   Why24 Appendix ANF: source Coefficient triple 1 3 9
-- statement:
--   The Why24 Appendix ANF construction uses the source Coefficient triple 1 3 9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part06.lean#L35-L37
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part06.lean#L35-L37

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part06
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
set_option maxRecDepth 2048

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_1_3_9 :
    sourceTripleCoefficient 1 3 9 = cubicGateCoefficient 1 3 9 := by sorry
