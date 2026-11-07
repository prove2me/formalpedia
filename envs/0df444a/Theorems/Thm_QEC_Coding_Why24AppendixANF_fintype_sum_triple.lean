-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_fintype_sum_triple
-- name    : QEC.Coding.Why24AppendixANF.fintype_sum_triple
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:52:29.949224+00:00
-- url     : https://prove2.me/theorems/d327ecbf-cb79-4131-a367-ab7bd8152b80
-- title:
--   Why24 Appendix ANF: fintype sum triple
-- statement:
--   Reassociate a sum over a right-associated triple product without exposing
--   the summand during rewriting.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Gate/ListStructure.lean#L57-L65
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Gate/ListStructure.lean#L57-L65

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Target
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_ListStructure
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
open scoped BigOperators

theorem QEC.Coding.Why24AppendixANF.fintype_sum_triple
    {A B C Value : Type*} [Fintype A] [Fintype B] [Fintype C]
    [AddCommMonoid Value] (value : A → B → C → Value) :
    (∑ entry : A × B × C, value entry.1 entry.2.1 entry.2.2) =
      ∑ first : A, ∑ second : B, ∑ third : C, value first second third := by sorry
