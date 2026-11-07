-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_hammingWeight_firstBlockWord_single_right
-- name    : QEC.Coding.HypergraphProduct.hammingWeight_firstBlockWord_single_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:18:47.846214+00:00
-- url     : https://prove2.me/theorems/f9bb5db6-0fca-4a87-80a3-d0b5fde33884
-- title:
--   Hypergraph Product: hamming Weight first Block Word single right
-- statement:
--   A first-block product with a basis word in the second factor has the
--   weight of its first factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Witness.lean#L111-L137
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Witness.lean#L111-L137

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_LowerBound
import Definitions.Def_QEC_Coding_HypergraphProduct_Locality
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Witness
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.hammingWeight_firstBlockWord_single_right
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype rowOne] [Fintype colOne]
    [Fintype rowTwo] [Fintype colTwo] [DecidableEq colTwo]
    (x : Word F colOne) (c₂ : colTwo) :
    HammingWeight
        (firstBlockWord (rowOne := rowOne) (rowTwo := rowTwo)
          x (Pi.single c₂ 1)) =
      HammingWeight x := by sorry
