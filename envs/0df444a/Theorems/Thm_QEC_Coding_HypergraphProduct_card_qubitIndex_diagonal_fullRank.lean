-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_card_qubitIndex_diagonal_fullRank
-- name    : QEC.Coding.HypergraphProduct.card_qubitIndex_diagonal_fullRank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:38:39.668207+00:00
-- url     : https://prove2.me/theorems/1dde2638-722f-45ed-aa54-fca0c8545652
-- title:
--   Hypergraph Product: card qubit Index diagonal full Rank
-- statement:
--   Exact blocklength of the diagonal full-rank construction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Diagonal.lean#L103-L114
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Diagonal.lean#L103-L114

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Formula
import Definitions.Def_QEC_Coding_HypergraphProduct_Locality
import Definitions.Def_QEC_Coding_HypergraphProduct_Diagonal
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.card_qubitIndex_diagonal_fullRank
    {Row Col : Type u}
    [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col]
    (H : Matrix Row Col (ZMod 2))
    (hFull : Function.Surjective (Matrix.toLin' H)) :
    Fintype.card (QubitIndex Row Col Row Col) =
      Fintype.card Col ^ 2 +
        (Fintype.card Col - Dimension (firstCode (diagonalData H))) ^ 2 := by sorry
