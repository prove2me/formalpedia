-- Prove2me | Theorems.Thm_QEC_Coding_SmallSetExpansion_IsSmallSetEdgeExpanding_of_internal_count
-- name    : QEC.Coding.SmallSetExpansion.IsSmallSetEdgeExpanding.of_internal_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:45:38.338206+00:00
-- url     : https://prove2.me/theorems/23dd22bc-1097-44bf-8813-dd4951d45ec2
-- title:
--   Is Small Set Edge Expanding: of internal count
-- statement:
--   Internal-edge control plus regularity upgrades to a two-set small-set
--   mixing estimate.  This is the elementary square-root interpolation used to
--   turn an Alon--Chung bound for `U` into the PK22 cross-count bound for `S,T`.
--
--   The internal estimate is requested at radius `2 * radius`, because it is
--   applied to `S ∪ T`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSquare.lean#L401-L466
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSquare.lean#L401-L466

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Mathlib.Data.Nat.Log
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}

theorem QEC.Coding.SmallSetExpansion.IsSmallSetEdgeExpanding.of_internal_count
    [Fintype V] [DecidableEq V]
    (M : WeightedGraph V) (radius degree : Nat) (internalConstant : ℝ)
    (hSymm : IsSymmetric M) (hRegular : IsRegular M degree)
    (hInternalNonnegative : 0 ≤ internalConstant)
    (hInternal : ∀ U : Finset V, U.card ≤ 2 * radius →
      (crossCount M U U : ℝ) ≤ internalConstant * U.card) :
    IsSmallSetEdgeExpanding M radius
      (Real.sqrt (2 * internalConstant * degree)) := by sorry
