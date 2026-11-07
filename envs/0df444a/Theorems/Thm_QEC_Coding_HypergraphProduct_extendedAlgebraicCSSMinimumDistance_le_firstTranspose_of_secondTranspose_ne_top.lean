-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_extendedAlgebraicCSSMinimumDistance_le_firstTranspose_of_secondTranspose_ne_top
-- name    : QEC.Coding.HypergraphProduct.extendedAlgebraicCSSMinimumDistance_le_firstTranspose_of_secondTranspose_ne_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:21:11.629024+00:00
-- url     : https://prove2.me/theorems/bc490090-3c41-49b3-8ce1-32cf5d37b8d3
-- title:
--   Hypergraph Product: extended Algebraic CSSMinimum Distance le first Transpose of second Transpose ne top
-- statement:
--   If the second transpose code is nonzero, the quantum distance is at most
--   the first transpose distance.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/UpperBound.lean#L126-L170
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/UpperBound.lean#L126-L170

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Witness
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_UpperBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.extendedAlgebraicCSSMinimumDistance_le_firstTranspose_of_secondTranspose_ne_top
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo)
    (hSecondTranspose :
      extendedMinimumDistance (secondTransposeCode D) ≠ ⊤) :
    extendedAlgebraicCSSMinimumDistance
        (binaryCSSCode D).xCode (binaryCSSCode D).zCode ≤
      extendedMinimumDistance (firstTransposeCode D) := by sorry
