-- Prove2me | Theorems.Thm_QEC_Coding_SmallSetExpansion_IsSmallSetEdgeExpanding_square_of_symmetric_regular
-- name    : QEC.Coding.SmallSetExpansion.IsSmallSetEdgeExpanding.square_of_symmetric_regular
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T01:46:37.204801+00:00
-- url     : https://prove2.me/theorems/52f613ab-dd53-4a15-aa4d-7f953fba8564
-- title:
--   Is Small Set Edge Expanding: square of symmetric regular
-- statement:
--   An internal dyadic variant of PK22's `lemma:exp2`.  Squaring a symmetric
--   regular small-set expander shrinks the radius by the degree and incurs a
--   `2 * lambda² * (log₂ degree + 1)` mixing constant.  This does not establish
--   the literal source coefficient `2 * lambda² * (1 + ln degree)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSquare.lean#L707-L768
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSquare.lean#L707-L768

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Mathlib.Data.Nat.Log
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}

theorem QEC.Coding.SmallSetExpansion.IsSmallSetEdgeExpanding.square_of_symmetric_regular
    [Fintype V] [DecidableEq V]
    {M : WeightedGraph V} {radius degree : Nat} {lambda : ℝ}
    (hLambda : 0 ≤ lambda)
    (hSymm : IsSymmetric M) (hRegular : IsRegular M degree)
    (hExpand : IsSmallSetEdgeExpanding M radius lambda) :
    IsSmallSetEdgeExpanding (square M) (radius / degree)
      (((Nat.log 2 degree + 1 : Nat) : ℝ) * (2 * lambda ^ 2)) := by sorry
