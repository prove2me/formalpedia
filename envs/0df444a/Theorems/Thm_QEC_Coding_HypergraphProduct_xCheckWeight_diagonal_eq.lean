-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_xCheckWeight_diagonal_eq
-- name    : QEC.Coding.HypergraphProduct.xCheckWeight_diagonal_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:02:05.063578+00:00
-- url     : https://prove2.me/theorems/c9436e49-85df-4fd8-ac4e-a522aa11408b
-- title:
--   Hypergraph Product: x Check Weight diagonal eq
-- statement:
--   Exact X-check row weights in the diagonal construction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Diagonal.lean#L169-L178
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Diagonal.lean#L169-L178

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Formula
import Definitions.Def_QEC_Coding_HypergraphProduct_Locality
import Definitions.Def_QEC_Coding_HypergraphProduct_Diagonal
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.xCheckWeight_diagonal_eq
    {Row Col : Type u}
    [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col]
    (H : Matrix Row Col (ZMod 2)) (r : Row) (c : Col) :
    HammingWeight
        (wordLinearMapTranspose (boundary1 (diagonalData H))
          (Pi.single (r, c) 1)) =
      rowWeight H r + columnWeight H c := by sorry
