-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_hammingWeight_secondBlockWord_single_left
-- name    : QEC.Coding.HypergraphProduct.hammingWeight_secondBlockWord_single_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:18:19.726448+00:00
-- url     : https://prove2.me/theorems/ee8147bc-7d87-41a4-94cc-b2ae519c5e6f
-- title:
--   Hypergraph Product: hamming Weight second Block Word single left
-- statement:
--   A second-block product with a basis word in the first factor has the
--   weight of its second factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Witness.lean#L200-L225
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Witness.lean#L200-L225

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_LowerBound
import Definitions.Def_QEC_Coding_HypergraphProduct_Locality
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Witness
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.hammingWeight_secondBlockWord_single_left
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype rowOne] [DecidableEq rowOne] [Fintype colOne]
    [Fintype rowTwo] [Fintype colTwo]
    (r₁ : rowOne) (y : Word F rowTwo) :
    HammingWeight
        (secondBlockWord (colOne := colOne) (colTwo := colTwo)
          (Pi.single r₁ 1) y) =
      HammingWeight y := by sorry
