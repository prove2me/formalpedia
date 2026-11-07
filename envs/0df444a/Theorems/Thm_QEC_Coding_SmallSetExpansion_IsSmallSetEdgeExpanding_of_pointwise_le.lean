-- Prove2me | Theorems.Thm_QEC_Coding_SmallSetExpansion_IsSmallSetEdgeExpanding_of_pointwise_le
-- name    : QEC.Coding.SmallSetExpansion.IsSmallSetEdgeExpanding.of_pointwise_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:47:56.419946+00:00
-- url     : https://prove2.me/theorems/f2c0dd6d-cfe1-49eb-8e06-884d13f53618
-- title:
--   Is Small Set Edge Expanding: of pointwise le
-- statement:
--   A pointwise subgraph inherits the same small-set expansion bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansion.lean#L254-L263
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansion.lean#L254-L263

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}

theorem QEC.Coding.SmallSetExpansion.IsSmallSetEdgeExpanding.of_pointwise_le
    {M N : WeightedGraph V} {radius : Nat} {lambda : ℝ}
    (hN : IsSmallSetEdgeExpanding N radius lambda)
    (hMN : ∀ v u, M v u ≤ N v u) :
    IsSmallSetEdgeExpanding M radius lambda := by sorry
