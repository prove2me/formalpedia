-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_hammingWeight_swapWord
-- name    : QEC.Coding.HypergraphProduct.hammingWeight_swapWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:38:46.736506+00:00
-- url     : https://prove2.me/theorems/75b7ccd9-1309-455d-a946-f86a2109a611
-- title:
--   Hypergraph Product: hamming Weight swap Word
-- statement:
--   Exchanging the two coordinate blocks preserves Hamming weight exactly.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Duality.lean#L39-L63
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Duality.lean#L39-L63

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Embedding
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Duality
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.hammingWeight_swapWord
    {F A B : Type*} [Zero F] [DecidableEq F] [Fintype A] [Fintype B]
    (x : Word F (Sum A B)) :
    HammingWeight (swapWord x) = HammingWeight x := by sorry
