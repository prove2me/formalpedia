-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_extendedAlgebraicCSSMinimumDistance_le_secondTranspose_of_firstTranspose_ne_top
-- name    : QEC.Coding.HypergraphProduct.extendedAlgebraicCSSMinimumDistance_le_secondTranspose_of_firstTranspose_ne_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:20:43.783207+00:00
-- url     : https://prove2.me/theorems/ab626245-e2e4-465b-a057-3d57b93abd59
-- title:
--   Hypergraph Product: extended Algebraic CSSMinimum Distance le second Transpose of first Transpose ne top
-- statement:
--   If the first transpose code is nonzero, the quantum distance is at most
--   the second transpose distance.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/UpperBound.lean#L174-L218
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/UpperBound.lean#L174-L218

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Witness
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_UpperBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.extendedAlgebraicCSSMinimumDistance_le_secondTranspose_of_firstTranspose_ne_top
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo)
    (hFirstTranspose :
      extendedMinimumDistance (firstTransposeCode D) ≠ ⊤) :
    extendedAlgebraicCSSMinimumDistance
        (binaryCSSCode D).xCode (binaryCSSCode D).zCode ≤
      extendedMinimumDistance (secondTransposeCode D) := by sorry
