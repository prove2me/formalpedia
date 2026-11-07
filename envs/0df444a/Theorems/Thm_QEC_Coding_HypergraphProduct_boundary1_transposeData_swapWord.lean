-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_boundary1_transposeData_swapWord
-- name    : QEC.Coding.HypergraphProduct.boundary1_transposeData_swapWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:38:33.172271+00:00
-- url     : https://prove2.me/theorems/23cb1667-85e0-4d28-bfb7-c7477cea7bb6
-- title:
--   Hypergraph Product: boundary1 transpose Data swap Word
-- statement:
--   The first boundary after transposing both Tanner matrices is the transpose
--   of the original second boundary, after exchanging the middle blocks.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Duality.lean#L95-L110
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Duality.lean#L95-L110

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Embedding
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Duality
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.boundary1_transposeData_swapWord
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo)
    (z : Word (ZMod 2) (QubitIndex rowOne colOne rowTwo colTwo)) :
    boundary1 (transposeData D) (swapWord z) =
      wordLinearMapTranspose (boundary2 D) z := by sorry
