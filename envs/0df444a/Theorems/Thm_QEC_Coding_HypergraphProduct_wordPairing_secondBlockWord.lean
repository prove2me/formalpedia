-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_wordPairing_secondBlockWord
-- name    : QEC.Coding.HypergraphProduct.wordPairing_secondBlockWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:12:26.023956+00:00
-- url     : https://prove2.me/theorems/bf50d5d7-18ea-43de-ac72-175ed2e535cd
-- title:
--   Hypergraph Product: word Pairing second Block Word
-- statement:
--   Pairing factorization on the second physical block.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Witness.lean#L61-L81
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Witness.lean#L61-L81

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_LowerBound
import Definitions.Def_QEC_Coding_HypergraphProduct_Locality
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Witness
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.wordPairing_secondBlockWord
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F]
    [Fintype rowOne] [Fintype colOne]
    [Fintype rowTwo] [Fintype colTwo]
    (x x' : Word F rowOne) (y y' : Word F rowTwo) :
    wordPairing
        (secondBlockWord (colOne := colOne) (colTwo := colTwo) x y)
        (secondBlockWord (colOne := colOne) (colTwo := colTwo) x' y') =
      wordPairing x x' * wordPairing y y' := by sorry
