-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_6_8
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_pair_6_8
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:34:31.928348+00:00
-- url     : https://prove2.me/theorems/ea8a1966-5cef-4417-8647-6a10f8bbf73b
-- title:
--   Why24 Appendix ANF: source Coefficient pair 6 8
-- statement:
--   The Why24 Appendix ANF construction uses the source Coefficient pair 6 8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Quadratic/PartD.lean#L40-L42
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Quadratic/PartD.lean#L40-L42

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_PartD
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
set_option maxRecDepth 2048

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_pair_6_8 :
    sourcePairCoefficient 6 8 = quadraticGateCoefficient 6 8 := by sorry
