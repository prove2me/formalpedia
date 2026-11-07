-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_eq_expandedGateCoefficient
-- name    : QEC.Coding.Why24AppendixANF.sourceCoefficient_eq_expandedGateCoefficient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:07:40.186281+00:00
-- url     : https://prove2.me/theorems/523ae2dc-76e0-49b0-a3d2-beaba46a65e3
-- title:
--   Why24 Appendix ANF: source Coefficient eq expanded Gate Coefficient
-- statement:
--   The normalized source coefficient equals the coefficient of the literal
--   linear/quadratic/cubic target sums for every squarefree support.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/SupportCertificate.lean#L244-L307
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/SupportCertificate.lean#L244-L307

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Target
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_SupportCertificate
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
open scoped BigOperators

theorem QEC.Coding.Why24AppendixANF.sourceCoefficient_eq_expandedGateCoefficient
    (support : Finset (Fin 10)) :
    sourceCoefficient support = expandedGateCoefficient support := by sorry
