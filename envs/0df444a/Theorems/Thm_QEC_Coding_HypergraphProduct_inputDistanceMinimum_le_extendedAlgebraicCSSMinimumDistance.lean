-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_inputDistanceMinimum_le_extendedAlgebraicCSSMinimumDistance
-- name    : QEC.Coding.HypergraphProduct.inputDistanceMinimum_le_extendedAlgebraicCSSMinimumDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:21:33.298675+00:00
-- url     : https://prove2.me/theorems/8499d32f-14cd-470d-aabe-a8466764d026
-- title:
--   Hypergraph Product: input Distance Minimum le extended Algebraic CSSMinimum Distance
-- statement:
--   Every nontrivial pure CSS logical representative has weight at least the
--   minimum of the four source-convention input distances.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/LowerBound.lean#L76-L127
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/LowerBound.lean#L76-L127

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Duality
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_LowerBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u

theorem QEC.Coding.HypergraphProduct.inputDistanceMinimum_le_extendedAlgebraicCSSMinimumDistance
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo) :
    inputDistanceMinimum D ≤
      extendedAlgebraicCSSMinimumDistance
        (binaryCSSCode D).xCode (binaryCSSCode D).zCode := by sorry
