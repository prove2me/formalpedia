-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_wordPairing_firstBlockWord
-- name    : QEC.Coding.HypergraphProduct.wordPairing_firstBlockWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:12:25.181943+00:00
-- url     : https://prove2.me/theorems/7c7ea922-f943-4802-bb5c-eb547cafafa1
-- title:
--   Hypergraph Product: word Pairing first Block Word
-- statement:
--   Pairing factorization on the first physical block.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Witness.lean#L38-L58
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Witness.lean#L38-L58

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_LowerBound
import Definitions.Def_QEC_Coding_HypergraphProduct_Locality
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Witness
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.wordPairing_firstBlockWord
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F]
    [Fintype rowOne] [Fintype colOne]
    [Fintype rowTwo] [Fintype colTwo]
    (x x' : Word F colOne) (y y' : Word F colTwo) :
    wordPairing
        (firstBlockWord (rowOne := rowOne) (rowTwo := rowTwo) x y)
        (firstBlockWord (rowOne := rowOne) (rowTwo := rowTwo) x' y') =
      wordPairing x x' * wordPairing y y' := by sorry
