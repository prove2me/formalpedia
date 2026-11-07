-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_wordPairing_single_left
-- name    : QEC.Coding.HypergraphProduct.wordPairing_single_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:11:34.250217+00:00
-- url     : https://prove2.me/theorems/1d4bbcdb-e41e-487b-ac1d-9160a33658d4
-- title:
--   Hypergraph Product: word Pairing single left
-- statement:
--   A basis word pairs with a word by evaluation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Witness.lean#L84-L94
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Witness.lean#L84-L94

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_LowerBound
import Definitions.Def_QEC_Coding_HypergraphProduct_Locality
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Witness
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.wordPairing_single_left
    {F : Type v} {A : Type u}
    [Field F] [Fintype F] [Fintype A] [DecidableEq A]
    (a : A) (x : Word F A) :
    wordPairing (Pi.single a 1) x = x a := by sorry
