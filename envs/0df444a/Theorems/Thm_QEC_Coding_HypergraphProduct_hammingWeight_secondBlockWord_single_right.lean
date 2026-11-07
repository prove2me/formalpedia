-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_hammingWeight_secondBlockWord_single_right
-- name    : QEC.Coding.HypergraphProduct.hammingWeight_secondBlockWord_single_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:18:21.218193+00:00
-- url     : https://prove2.me/theorems/a4b0f294-8784-47ff-875b-f9f2aa63bc70
-- title:
--   Hypergraph Product: hamming Weight second Block Word single right
-- statement:
--   A second-block product with a basis word in the second factor has the
--   weight of its first factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Witness.lean#L171-L196
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Witness.lean#L171-L196

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_LowerBound
import Definitions.Def_QEC_Coding_HypergraphProduct_Locality
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Witness
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.hammingWeight_secondBlockWord_single_right
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype rowOne] [Fintype colOne]
    [Fintype rowTwo] [DecidableEq rowTwo] [Fintype colTwo]
    (x : Word F rowOne) (r₂ : rowTwo) :
    HammingWeight
        (secondBlockWord (colOne := colOne) (colTwo := colTwo)
          x (Pi.single r₂ 1)) =
      HammingWeight x := by sorry
