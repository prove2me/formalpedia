-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_3_7
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_pair_3_7
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:30:49.689014+00:00
-- url     : https://prove2.me/theorems/0ea7b1c6-721a-4ec6-a69e-1aed74e4ae77
-- title:
--   Why24 Appendix ANF: source Coefficient pair 3 7
-- statement:
--   The Why24 Appendix ANF construction uses the source Coefficient pair 3 7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Quadratic/PartC.lean#L30-L32
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Quadratic/PartC.lean#L30-L32

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_PartC
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
set_option maxRecDepth 2048

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_pair_3_7 :
    sourcePairCoefficient 3 7 = quadraticGateCoefficient 3 7 := by sorry
