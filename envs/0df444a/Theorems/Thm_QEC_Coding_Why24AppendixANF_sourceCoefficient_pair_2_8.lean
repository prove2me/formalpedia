-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_2_8
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_pair_2_8
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:29:02.809237+00:00
-- url     : https://prove2.me/theorems/db40325e-631b-47d5-ba78-cd084d5e6edd
-- title:
--   Why24 Appendix ANF: source Coefficient pair 2 8
-- statement:
--   The Why24 Appendix ANF construction uses the source Coefficient pair 2 8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Quadratic/PartB.lean#L80-L82
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Quadratic/PartB.lean#L80-L82

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_PartB
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
set_option maxRecDepth 2048

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_pair_2_8 :
    sourcePairCoefficient 2 8 = quadraticGateCoefficient 2 8 := by sorry
