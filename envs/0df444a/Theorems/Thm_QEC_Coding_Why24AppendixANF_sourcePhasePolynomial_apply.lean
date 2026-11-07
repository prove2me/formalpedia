-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourcePhasePolynomial_apply
-- name    : QEC.Coding.Why24AppendixANF.sourcePhasePolynomial_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:06:59.185563+00:00
-- url     : https://prove2.me/theorems/8c069a57-8c65-48a1-a256-14bbecd6715f
-- title:
--   Why24 Appendix ANF: source Phase Polynomial apply
-- statement:
--   Coefficients of the sparse source polynomial are exactly the normalized
--   ordered-tensor coefficients certified in the preceding modules.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Symbolic.lean#L65-L83
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Symbolic.lean#L65-L83

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_Certificate
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Certificate
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Symbolic
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
open scoped BigOperators
open Why24BooleanANF

theorem QEC.Coding.Why24AppendixANF.sourcePhasePolynomial_apply (monomial : Monomial 10) :
    sourcePhasePolynomial.coeff monomial = sourceCoefficient monomial.support := by sorry
