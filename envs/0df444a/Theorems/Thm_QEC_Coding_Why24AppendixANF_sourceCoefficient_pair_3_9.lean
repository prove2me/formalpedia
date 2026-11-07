-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_3_9
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_pair_3_9
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:30:50.670647+00:00
-- url     : https://prove2.me/theorems/bd15a3a4-c876-4e09-a8c6-825fe439b674
-- title:
--   Why24 Appendix ANF: source Coefficient pair 3 9
-- statement:
--   The Why24 Appendix ANF construction uses the source Coefficient pair 3 9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Quadratic/PartC.lean#L40-L42
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Quadratic/PartC.lean#L40-L42

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_PartC
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
set_option maxRecDepth 2048

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_pair_3_9 :
    sourcePairCoefficient 3 9 = quadraticGateCoefficient 3 9 := by sorry
