-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_extendedAlgebraicCSSMinimumDistance_le_first_of_second_ne_top
-- name    : QEC.Coding.HypergraphProduct.extendedAlgebraicCSSMinimumDistance_le_first_of_second_ne_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:15:51.933205+00:00
-- url     : https://prove2.me/theorems/44c6b96c-4391-4f15-8c61-f06e2c6c81a6
-- title:
--   Hypergraph Product: extended Algebraic CSSMinimum Distance le first of second ne top
-- statement:
--   If the second primal code is nonzero, the quantum distance is at most the
--   first primal distance.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/UpperBound.lean#L32-L75
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/UpperBound.lean#L32-L75

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Witness
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_UpperBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.extendedAlgebraicCSSMinimumDistance_le_first_of_second_ne_top
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo)
    (hSecond : extendedMinimumDistance (secondCode D) ≠ ⊤) :
    extendedAlgebraicCSSMinimumDistance
        (binaryCSSCode D).xCode (binaryCSSCode D).zCode ≤
      extendedMinimumDistance (firstCode D) := by sorry
