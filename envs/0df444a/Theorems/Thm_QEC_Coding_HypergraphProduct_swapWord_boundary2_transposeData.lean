-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_swapWord_boundary2_transposeData
-- name    : QEC.Coding.HypergraphProduct.swapWord_boundary2_transposeData
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:38:44.271296+00:00
-- url     : https://prove2.me/theorems/f180a16c-5d4f-4544-aa30-a076421b6181
-- title:
--   Hypergraph Product: swap Word boundary2 transpose Data
-- statement:
--   The second boundary after transposing both Tanner matrices becomes the
--   transpose of the original first boundary after exchanging middle blocks.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Duality.lean#L114-L135
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Duality.lean#L114-L135

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Embedding
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Duality
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.swapWord_boundary2_transposeData
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo)
    (w : Word (ZMod 2) (C0Index rowOne colTwo)) :
    swapWord (boundary2 (transposeData D) w) =
      wordLinearMapTranspose (boundary1 D) w := by sorry
