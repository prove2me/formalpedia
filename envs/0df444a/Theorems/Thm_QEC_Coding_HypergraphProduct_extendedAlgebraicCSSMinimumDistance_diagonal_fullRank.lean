-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_extendedAlgebraicCSSMinimumDistance_diagonal_fullRank
-- name    : QEC.Coding.HypergraphProduct.extendedAlgebraicCSSMinimumDistance_diagonal_fullRank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:39:29.811424+00:00
-- url     : https://prove2.me/theorems/5cc0a7c6-b74f-4057-be1d-92dc4dafd271
-- title:
--   Hypergraph Product: extended Algebraic CSSMinimum Distance diagonal full Rank
-- statement:
--   The diagonal full-rank quantum distance equals the source-convention
--   distance of the classical code, including the zero-code infinity case.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Diagonal.lean#L133-L166
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Diagonal.lean#L133-L166

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Formula
import Definitions.Def_QEC_Coding_HypergraphProduct_Locality
import Definitions.Def_QEC_Coding_HypergraphProduct_Diagonal
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.extendedAlgebraicCSSMinimumDistance_diagonal_fullRank
    {Row Col : Type u}
    [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col]
    (H : Matrix Row Col (ZMod 2))
    (hFull : Function.Surjective (Matrix.toLin' H)) :
    extendedAlgebraicCSSMinimumDistance
        (binaryCSSCode (diagonalData H)).xCode
        (binaryCSSCode (diagonalData H)).zCode =
      extendedMinimumDistance (firstCode (diagonalData H)) := by sorry
