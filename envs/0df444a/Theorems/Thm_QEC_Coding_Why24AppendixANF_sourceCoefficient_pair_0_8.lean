-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_0_8
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_pair_0_8
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:26:31.905591+00:00
-- url     : https://prove2.me/theorems/be83c108-8895-49a8-957e-bdeadd709384
-- title:
--   Why24 Appendix ANF: source Coefficient pair 0 8
-- statement:
--   The Why24 Appendix ANF construction uses the source Coefficient pair 0 8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Quadratic/PartA.lean#L50-L52
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Quadratic/PartA.lean#L50-L52

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_PartA
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
set_option maxRecDepth 2048

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_pair_0_8 :
    sourcePairCoefficient 0 8 = quadraticGateCoefficient 0 8 := by sorry
