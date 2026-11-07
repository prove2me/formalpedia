-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_extendedAlgebraicCSSMinimumDistance_le_second_of_first_ne_top
-- name    : QEC.Coding.HypergraphProduct.extendedAlgebraicCSSMinimumDistance_le_second_of_first_ne_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:21:05.353215+00:00
-- url     : https://prove2.me/theorems/fda905bf-ccdd-42aa-bdd8-1587385da8bc
-- title:
--   Hypergraph Product: extended Algebraic CSSMinimum Distance le second of first ne top
-- statement:
--   If the first primal code is nonzero, the quantum distance is at most the
--   second primal distance.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/UpperBound.lean#L79-L122
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/UpperBound.lean#L79-L122

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Witness
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_UpperBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.extendedAlgebraicCSSMinimumDistance_le_second_of_first_ne_top
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo)
    (hFirst : extendedMinimumDistance (firstCode D) ≠ ⊤) :
    extendedAlgebraicCSSMinimumDistance
        (binaryCSSCode D).xCode (binaryCSSCode D).zCode ≤
      extendedMinimumDistance (secondCode D) := by sorry
