-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_cubicGateTriples_ordered
-- name    : QEC.Coding.Why24AppendixANF.cubicGateTriples_ordered
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:09:37.864651+00:00
-- url     : https://prove2.me/theorems/673e0419-eaa9-4240-b8e6-81f547ea8701
-- title:
--   Why24 Appendix ANF: cubic Gate Triples ordered
-- statement:
--   Every printed cubic triple is strictly increasing.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Gate/ListStructure.lean#L40-L46
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Gate/ListStructure.lean#L40-L46

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Target
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_ListStructure
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
open scoped BigOperators

theorem QEC.Coding.Why24AppendixANF.cubicGateTriples_ordered (triple : Fin 10 × Fin 10 × Fin 10)
    (htriple : triple ∈ cubicGateTriples) :
    triple.1 < triple.2.1 ∧ triple.2.1 < triple.2.2 := by sorry
