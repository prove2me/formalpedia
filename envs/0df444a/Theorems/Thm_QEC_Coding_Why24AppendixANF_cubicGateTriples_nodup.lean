-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_cubicGateTriples_nodup
-- name    : QEC.Coding.Why24AppendixANF.cubicGateTriples_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:07:22.878342+00:00
-- url     : https://prove2.me/theorems/2b96fc2a-1932-469a-b1a0-a42452e3f5bd
-- title:
--   Why24 Appendix ANF: cubic Gate Triples nodup
-- statement:
--   The printed cubic gate list has no repeated triple.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Gate/ListStructure.lean#L36-L37
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Gate/ListStructure.lean#L36-L37

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Target
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_ListStructure
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
open scoped BigOperators

theorem QEC.Coding.Why24AppendixANF.cubicGateTriples_nodup : cubicGateTriples.Nodup := by sorry
