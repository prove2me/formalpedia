-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_0_2
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_pair_0_2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:26:25.282286+00:00
-- url     : https://prove2.me/theorems/abeda1f6-1834-4aeb-a85c-eb03c834a51c
-- title:
--   Why24 Appendix ANF: source Coefficient pair 0 2
-- statement:
--   The Why24 Appendix ANF construction uses the source Coefficient pair 0 2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Quadratic/PartA.lean#L20-L22
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Quadratic/PartA.lean#L20-L22

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_PartA
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
set_option maxRecDepth 2048

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_pair_0_2 :
    sourcePairCoefficient 0 2 = quadraticGateCoefficient 0 2 := by sorry
