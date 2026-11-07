-- Prove2me | Theorems.Thm_QEC_Coding_SmallSetExpansion_IsSmallSetEdgeExpanding_disjointUnion
-- name    : QEC.Coding.SmallSetExpansion.IsSmallSetEdgeExpanding.disjointUnion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:47:49.210506+00:00
-- url     : https://prove2.me/theorems/35e0df54-c980-4965-a011-30d7bf0e0df7
-- title:
--   Is Small Set Edge Expanding: disjoint Union
-- statement:
--   A disjoint union of small-set expanders has the same mixing constant.
--   The Cauchy--Schwarz step is essential: there is no loss by the number of
--   components.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansion.lean#L209-L242
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansion.lean#L209-L242

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}

theorem QEC.Coding.SmallSetExpansion.IsSmallSetEdgeExpanding.disjointUnion
    {I : Type*} [Fintype I] [DecidableEq I] [DecidableEq V]
    {M : I → WeightedGraph V} {radius : Nat} {lambda : ℝ}
    (hLambda : 0 ≤ lambda)
    (hM : ∀ i, IsSmallSetEdgeExpanding (M i) radius lambda) :
    IsSmallSetEdgeExpanding (disjointUnion M) radius lambda := by sorry
