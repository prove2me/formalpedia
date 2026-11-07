-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_0_1_8
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_0_1_8
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:37:08.67766+00:00
-- url     : https://prove2.me/theorems/4e93059f-02ce-4dba-8b5e-4c6c73c25cb9
-- title:
--   Why24 Appendix ANF: source Coefficient triple 0 1 8
-- statement:
--   The Why24 Appendix ANF construction uses the source Coefficient triple 0 1 8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part00.lean#L40-L42
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Cubic/Part00.lean#L40-L42

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Probe
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part00
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
set_option maxRecDepth 2048

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_0_1_8 :
    sourceTripleCoefficient 0 1 8 = cubicGateCoefficient 0 1 8 := by sorry
