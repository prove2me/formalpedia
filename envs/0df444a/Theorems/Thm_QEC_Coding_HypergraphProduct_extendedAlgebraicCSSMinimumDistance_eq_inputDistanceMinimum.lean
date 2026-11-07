-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_extendedAlgebraicCSSMinimumDistance_eq_inputDistanceMinimum
-- name    : QEC.Coding.HypergraphProduct.extendedAlgebraicCSSMinimumDistance_eq_inputDistanceMinimum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:20:53.887337+00:00
-- url     : https://prove2.me/theorems/7f089e4e-5b35-4b45-a6ad-9489870072bf
-- title:
--   Hypergraph Product: extended Algebraic CSSMinimum Distance eq input Distance Minimum
-- statement:
--   Under exactly the source equality condition, the general HGP distance is
--   the minimum of the four input distances.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Formula.lean#L37-L60
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Formula.lean#L37-L60

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_UpperBound
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Formula
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u

theorem QEC.Coding.HypergraphProduct.extendedAlgebraicCSSMinimumDistance_eq_inputDistanceMinimum
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo)
    (hEquality : DistanceEqualityCondition D) :
    extendedAlgebraicCSSMinimumDistance
        (binaryCSSCode D).xCode (binaryCSSCode D).zCode =
      inputDistanceMinimum D := by sorry
