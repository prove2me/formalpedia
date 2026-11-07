-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_zCheckWeight_diagonal_eq
-- name    : QEC.Coding.HypergraphProduct.zCheckWeight_diagonal_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:01:25.076878+00:00
-- url     : https://prove2.me/theorems/c4c68c70-78ad-4122-a04d-162ebb10bdfe
-- title:
--   Hypergraph Product: z Check Weight diagonal eq
-- statement:
--   Exact Z-check row weights in the diagonal construction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Diagonal.lean#L181-L188
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Diagonal.lean#L181-L188

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Formula
import Definitions.Def_QEC_Coding_HypergraphProduct_Locality
import Definitions.Def_QEC_Coding_HypergraphProduct_Diagonal
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.zCheckWeight_diagonal_eq
    {Row Col : Type u}
    [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col]
    (H : Matrix Row Col (ZMod 2)) (c : Col) (r : Row) :
    HammingWeight (boundary2 (diagonalData H) (Pi.single (c, r) 1)) =
      rowWeight H r + columnWeight H c := by sorry
