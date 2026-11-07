-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_8_9
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_pair_8_9
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:34:46.450668+00:00
-- url     : https://prove2.me/theorems/6814d5e0-49e3-4760-855e-4c50ac15fd6e
-- title:
--   Why24 Appendix ANF: source Coefficient pair 8 9
-- statement:
--   The Why24 Appendix ANF construction uses the source Coefficient pair 8 9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Quadratic/PartD.lean#L60-L62
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Quadratic/PartD.lean#L60-L62

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_PartD
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
set_option maxRecDepth 2048

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_pair_8_9 :
    sourcePairCoefficient 8 9 = quadraticGateCoefficient 8 9 := by sorry
