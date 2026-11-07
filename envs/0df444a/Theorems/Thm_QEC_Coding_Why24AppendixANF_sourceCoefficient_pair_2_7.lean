-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_2_7
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_pair_2_7
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:28:38.686922+00:00
-- url     : https://prove2.me/theorems/1986188d-d514-4c2b-81b5-29fa0f051deb
-- title:
--   Why24 Appendix ANF: source Coefficient pair 2 7
-- statement:
--   The Why24 Appendix ANF construction uses the source Coefficient pair 2 7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Quadratic/PartB.lean#L75-L77
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Quadratic/PartB.lean#L75-L77

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_PartB
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
set_option maxRecDepth 2048

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_pair_2_7 :
    sourcePairCoefficient 2 7 = quadraticGateCoefficient 2 7 := by sorry
