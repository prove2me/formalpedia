-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_wordPairing_single_right
-- name    : QEC.Coding.HypergraphProduct.wordPairing_single_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:11:43.024473+00:00
-- url     : https://prove2.me/theorems/d9c08d2e-8d5e-4c45-9462-db2c252c0805
-- title:
--   Hypergraph Product: word Pairing single right
-- statement:
--   Evaluation is also the pairing with a basis word on the right.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Witness.lean#L97-L107
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Witness.lean#L97-L107

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_LowerBound
import Definitions.Def_QEC_Coding_HypergraphProduct_Locality
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Witness
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.wordPairing_single_right
    {F : Type v} {A : Type u}
    [Field F] [Fintype F] [Fintype A] [DecidableEq A]
    (x : Word F A) (a : A) :
    wordPairing x (Pi.single a 1) = x a := by sorry
