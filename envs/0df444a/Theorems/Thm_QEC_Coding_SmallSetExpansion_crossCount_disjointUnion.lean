-- Prove2me | Theorems.Thm_QEC_Coding_SmallSetExpansion_crossCount_disjointUnion
-- name    : QEC.Coding.SmallSetExpansion.crossCount_disjointUnion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:45:56.812202+00:00
-- url     : https://prove2.me/theorems/7f64ca26-9774-41d7-9a88-5895476db255
-- title:
--   Small Set Expansion: cross Count disjoint Union
-- statement:
--   Cross counts in a disjoint union split as the sum of the component cross
--   counts of the corresponding fibers.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansion.lean#L173-L204
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansion.lean#L173-L204

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}

theorem QEC.Coding.SmallSetExpansion.crossCount_disjointUnion
    {I : Type*} [Fintype I] [DecidableEq I] [DecidableEq V]
    (M : I → WeightedGraph V) (S T : Finset (I × V)) :
    crossCount (disjointUnion M) S T =
      ∑ i, crossCount (M i) (productFiber S i) (productFiber T i) := by sorry
