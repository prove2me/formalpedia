-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_not_mem_firstCoboundaryCheckCode_of_pairing_cycle_ne_zero
-- name    : QEC.Coding.HypergraphProduct.not_mem_firstCoboundaryCheckCode_of_pairing_cycle_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:15:43.168981+00:00
-- url     : https://prove2.me/theorems/6dc121e7-4446-47c7-a2f1-8479876354cc
-- title:
--   Hypergraph Product: not mem first Coboundary Check Code of pairing cycle ne zero
-- statement:
--   A cocycle that pairs nontrivially with a cycle cannot be a coboundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Witness.lean#L415-L440
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Witness.lean#L415-L440

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_LowerBound
import Definitions.Def_QEC_Coding_HypergraphProduct_Locality
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Witness
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.not_mem_firstCoboundaryCheckCode_of_pairing_cycle_ne_zero
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo)
    (z u : Word F (QubitIndex rowOne colOne rowTwo colTwo))
    (huCycle : u ∈ (chainComplex D).middleCycleCode.carrier)
    (hPair : wordPairing z u ≠ 0) :
    z ∉ (chainComplex D).firstCoboundaryCheckCode.carrier := by sorry
