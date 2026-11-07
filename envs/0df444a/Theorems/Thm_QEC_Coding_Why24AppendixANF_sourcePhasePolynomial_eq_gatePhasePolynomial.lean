-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_sourcePhasePolynomial_eq_gatePhasePolynomial
-- name    : QEC.Coding.Why24AppendixANF.sourcePhasePolynomial_eq_gatePhasePolynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:51:18.361188+00:00
-- url     : https://prove2.me/theorems/b24168ba-f905-49cc-b3e3-bdc7524caf7e
-- title:
--   Why24 Appendix ANF: source Phase Polynomial eq gate Phase Polynomial
-- statement:
--   The compositional trace ANF is exactly the literal Appendix-A gate ANF.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/SupportCertificate.lean#L310-L316
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/SupportCertificate.lean#L310-L316

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Target
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_SupportCertificate
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
open scoped BigOperators

theorem QEC.Coding.Why24AppendixANF.sourcePhasePolynomial_eq_gatePhasePolynomial :
    sourcePhasePolynomial = gatePhasePolynomial := by sorry
