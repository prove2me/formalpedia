-- Prove2me | Theorems.Thm_QEC_Coding_SmallSetExpansion_IsSmallSetEdgeExpanding_relabel
-- name    : QEC.Coding.SmallSetExpansion.IsSmallSetEdgeExpanding.relabel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:47:30.792083+00:00
-- url     : https://prove2.me/theorems/b9c63945-894b-4ba0-b625-e06f0a492858
-- title:
--   Is Small Set Edge Expanding: relabel
-- statement:
--   Small-set expansion is invariant under a bijective relabelling of the
--   vertices.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansion.lean#L116-L124
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansion.lean#L116-L124

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}

theorem QEC.Coding.SmallSetExpansion.IsSmallSetEdgeExpanding.relabel
    {U : Type*} [DecidableEq V] [DecidableEq U]
    {M : WeightedGraph V} {radius : Nat} {lambda : ℝ}
    (hM : IsSmallSetEdgeExpanding M radius lambda) (e : V ≃ U) :
    IsSmallSetEdgeExpanding (relabel e M) radius lambda := by sorry
