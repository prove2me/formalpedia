-- Prove2me | Theorems.Thm_QEC_Coding_why24AppendixGateListANF_eq_gatePhasePolynomial
-- name    : QEC.Coding.why24AppendixGateListANF_eq_gatePhasePolynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:53:32.683076+00:00
-- url     : https://prove2.me/theorems/cd56b8ff-0a22-4a34-b827-b009c561d99e
-- title:
--   Coding: why24 Appendix Gate List ANF eq gate Phase Polynomial
-- statement:
--   The literal Appendix-A gate list denotes exactly the sparse target ANF.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Gate/Data.lean#L178-L182
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Gate/Data.lean#L178-L182

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Evaluation
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_Certificate
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_Data
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators
open Why24BooleanANF
open Why24AppendixANF

theorem QEC.Coding.why24AppendixGateListANF_eq_gatePhasePolynomial :
    why24AppendixGateListANF why24AppendixGateList = gatePhasePolynomial := by sorry
