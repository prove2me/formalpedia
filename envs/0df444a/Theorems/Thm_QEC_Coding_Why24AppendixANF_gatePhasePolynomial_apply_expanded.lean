-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_gatePhasePolynomial_apply_expanded
-- name    : QEC.Coding.Why24AppendixANF.gatePhasePolynomial_apply_expanded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:07:15.174127+00:00
-- url     : https://prove2.me/theorems/b682a932-f978-4f1f-b4e3-789b0feb8c2a
-- title:
--   Why24 Appendix ANF: gate Phase Polynomial apply expanded
-- statement:
--   Coefficient of the target polynomial before support-cardinality
--   normalization.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Target.lean#L105-L178
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Target.lean#L105-L178

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Symbolic
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Target
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
open scoped BigOperators
open Why24BooleanANF

theorem QEC.Coding.Why24AppendixANF.gatePhasePolynomial_apply_expanded (monomial : Monomial 10) :
    gatePhasePolynomial.coeff monomial = expandedGateCoefficient monomial.support := by sorry
