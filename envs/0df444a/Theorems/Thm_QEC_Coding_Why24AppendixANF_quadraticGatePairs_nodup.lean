-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_quadraticGatePairs_nodup
-- name    : QEC.Coding.Why24AppendixANF.quadraticGatePairs_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:07:51.283769+00:00
-- url     : https://prove2.me/theorems/a051e1a0-7348-4c89-8839-8f349be141c2
-- title:
--   Why24 Appendix ANF: quadratic Gate Pairs nodup
-- statement:
--   The printed quadratic gate list has no repeated pair.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Gate/ListStructure.lean#L18-L19
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Gate/ListStructure.lean#L18-L19

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Target
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_ListStructure
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
open scoped BigOperators

theorem QEC.Coding.Why24AppendixANF.quadraticGatePairs_nodup : quadraticGatePairs.Nodup := by sorry
