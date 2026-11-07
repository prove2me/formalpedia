-- Prove2me | Theorems.Thm_QEC_Coding_LocallyMinimalDistance_elementaryBoundaryMoves_subset_middleBoundaryCode
-- name    : QEC.Coding.LocallyMinimalDistance.elementaryBoundaryMoves_subset_middleBoundaryCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:17:48.075295+00:00
-- url     : https://prove2.me/theorems/32c9f913-ba53-48a6-80ab-daee60291ca5
-- title:
--   Locally Minimal Distance: elementary Boundary Moves subset middle Boundary Code
-- statement:
--   Every elementary boundary move is an actual middle boundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocallyMinimalDistance.lean#L105-L114
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocallyMinimalDistance.lean#L105-L114

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.Order.Lattice.Nat
import Definitions.Def_QEC_Coding_ExpanderCodes_LocallyMinimalDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LocallyMinimalDistance
universe u v
variable {C : Type*} [AddCommGroup C]

theorem QEC.Coding.LocallyMinimalDistance.elementaryBoundaryMoves_subset_middleBoundaryCode
    {F : Type u} {ι κ₀ κ₂ : Type v} [Field F] [Fintype F]
    [Fintype ι] [Fintype κ₀] [Fintype κ₂]
    (K : ChainComplexData F (Word F κ₀) (Word F ι) (Word F κ₂))
    (m : Word F ι) (hm : m ∈ elementaryBoundaryMoves K) :
    m ∈ K.middleBoundaryCode.carrier := by sorry
