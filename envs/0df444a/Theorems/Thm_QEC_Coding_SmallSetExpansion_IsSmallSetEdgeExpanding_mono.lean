-- Prove2me | Theorems.Thm_QEC_Coding_SmallSetExpansion_IsSmallSetEdgeExpanding_mono
-- name    : QEC.Coding.SmallSetExpansion.IsSmallSetEdgeExpanding.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:48:03.715213+00:00
-- url     : https://prove2.me/theorems/f047b6a4-7ffe-4791-bd93-c78983b01df1
-- title:
--   Is Small Set Edge Expanding: mono
-- statement:
--   Small-set expansion is monotone under shrinking the radius and enlarging
--   the mixing constant.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansion.lean#L267-L278
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansion.lean#L267-L278

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}

theorem QEC.Coding.SmallSetExpansion.IsSmallSetEdgeExpanding.mono
    {M : WeightedGraph V} {radius radius' : Nat} {lambda lambda' : ℝ}
    (hExpand : IsSmallSetEdgeExpanding M radius lambda)
    (hRadius : radius' ≤ radius) (hLambda : lambda ≤ lambda') :
    IsSmallSetEdgeExpanding M radius' lambda' := by sorry
