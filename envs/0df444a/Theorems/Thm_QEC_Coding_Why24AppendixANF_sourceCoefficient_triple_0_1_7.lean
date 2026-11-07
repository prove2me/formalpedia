-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_0_1_7
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_0_1_7
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:37:17.74219+00:00
-- url     : https://prove2.me/theorems/b6312cac-0030-4861-a9ad-ceb20aa3bba2
-- title:
--   Why24 Appendix ANF: source Coefficient triple 0 1 7
-- statement:
--   The Why24 Appendix ANF construction uses the source Coefficient triple 0 1 7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part00.lean#L35-L37
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part00.lean#L35-L37

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Probe
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part00
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
set_option maxRecDepth 2048

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_0_1_7 :
    sourceTripleCoefficient 0 1 7 = cubicGateCoefficient 0 1 7 := by sorry
