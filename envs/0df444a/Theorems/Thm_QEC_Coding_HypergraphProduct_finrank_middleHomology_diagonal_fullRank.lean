-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_finrank_middleHomology_diagonal_fullRank
-- name    : QEC.Coding.HypergraphProduct.finrank_middleHomology_diagonal_fullRank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:39:21.009984+00:00
-- url     : https://prove2.me/theorems/a2eb057c-35f8-4bc1-b9c3-9e49034e76bd
-- title:
--   Hypergraph Product: finrank middle Homology diagonal full Rank
-- statement:
--   Exact encoded dimension of the diagonal full-rank construction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Diagonal.lean#L117-L129
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Diagonal.lean#L117-L129

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Formula
import Definitions.Def_QEC_Coding_HypergraphProduct_Locality
import Definitions.Def_QEC_Coding_HypergraphProduct_Diagonal
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.finrank_middleHomology_diagonal_fullRank
    {Row Col : Type u}
    [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col]
    (H : Matrix Row Col (ZMod 2))
    (hFull : Function.Surjective (Matrix.toLin' H)) :
    Module.finrank (ZMod 2) (chainComplex (diagonalData H)).middleHomology =
      Dimension (firstCode (diagonalData H)) ^ 2 := by sorry
