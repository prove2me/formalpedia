-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_hammingWeight_firstBlockWord_single_left
-- name    : QEC.Coding.HypergraphProduct.hammingWeight_firstBlockWord_single_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:19:09.896566+00:00
-- url     : https://prove2.me/theorems/53dc9e4e-038f-40e0-ae31-9ed6072e0d12
-- title:
--   Hypergraph Product: hamming Weight first Block Word single left
-- statement:
--   A first-block product with a basis word in the first factor has the
--   weight of its second factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Witness.lean#L141-L167
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Witness.lean#L141-L167

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_LowerBound
import Definitions.Def_QEC_Coding_HypergraphProduct_Locality
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Witness
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.hammingWeight_firstBlockWord_single_left
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype rowOne] [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [Fintype colTwo]
    (c₁ : colOne) (y : Word F colTwo) :
    HammingWeight
        (firstBlockWord (rowOne := rowOne) (rowTwo := rowTwo)
          (Pi.single c₁ 1) y) =
      HammingWeight y := by sorry
