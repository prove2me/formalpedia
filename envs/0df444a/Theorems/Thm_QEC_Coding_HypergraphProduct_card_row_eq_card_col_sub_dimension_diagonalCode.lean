-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_card_row_eq_card_col_sub_dimension_diagonalCode
-- name    : QEC.Coding.HypergraphProduct.card_row_eq_card_col_sub_dimension_diagonalCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:22:59.622231+00:00
-- url     : https://prove2.me/theorems/21bce2ae-f64e-44aa-9016-f133dd32b2a5
-- title:
--   Hypergraph Product: card row eq card col sub dimension diagonal Code
-- statement:
--   Full row rank identifies the check count with `n - k`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Diagonal.lean#L88-L100
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Diagonal.lean#L88-L100

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Formula
import Definitions.Def_QEC_Coding_HypergraphProduct_Locality
import Definitions.Def_QEC_Coding_HypergraphProduct_Diagonal
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.card_row_eq_card_col_sub_dimension_diagonalCode
    {Row Col : Type u}
    [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col]
    (H : Matrix Row Col (ZMod 2))
    (hFull : Function.Surjective (Matrix.toLin' H)) :
    Fintype.card Row =
      Fintype.card Col - Dimension (firstCode (diagonalData H)) := by sorry
