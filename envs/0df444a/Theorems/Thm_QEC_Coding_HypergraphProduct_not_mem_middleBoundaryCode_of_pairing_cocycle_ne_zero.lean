-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_not_mem_middleBoundaryCode_of_pairing_cocycle_ne_zero
-- name    : QEC.Coding.HypergraphProduct.not_mem_middleBoundaryCode_of_pairing_cocycle_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:15:39.781206+00:00
-- url     : https://prove2.me/theorems/b92e9fb3-8253-4e0f-a572-81ee30aceb9e
-- title:
--   Hypergraph Product: not mem middle Boundary Code of pairing cocycle ne zero
-- statement:
--   A cycle that pairs nontrivially with a cocycle cannot be a boundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Witness.lean#L389-L412
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Witness.lean#L389-L412

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_LowerBound
import Definitions.Def_QEC_Coding_HypergraphProduct_Locality
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Witness
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.not_mem_middleBoundaryCode_of_pairing_cocycle_ne_zero
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo)
    (z u : Word F (QubitIndex rowOne colOne rowTwo colTwo))
    (huCocycle : u ∈ (chainComplex D).middleCocycleCode.carrier)
    (hPair : wordPairing u z ≠ 0) :
    z ∉ (chainComplex D).middleBoundaryCode.carrier := by sorry
