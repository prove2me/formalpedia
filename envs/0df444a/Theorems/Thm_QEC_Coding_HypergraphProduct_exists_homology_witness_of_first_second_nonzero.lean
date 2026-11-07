-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_exists_homology_witness_of_first_second_nonzero
-- name    : QEC.Coding.HypergraphProduct.exists_homology_witness_of_first_second_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:19:53.285841+00:00
-- url     : https://prove2.me/theorems/079cdc5d-99fc-4b24-b73d-1fc39742b551
-- title:
--   Hypergraph Product: exists homology witness of first second nonzero
-- statement:
--   A nonzero first-code word has a homologically nontrivial first-block
--   representative of the same weight whenever the second code is nonzero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Witness.lean#L444-L476
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Witness.lean#L444-L476

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_LowerBound
import Definitions.Def_QEC_Coding_HypergraphProduct_Locality
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Witness
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.exists_homology_witness_of_first_second_nonzero
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo)
    (x : Word (ZMod 2) colOne) (hx : x ∈ (firstCode D).carrier)
    (hx0 : x ≠ 0)
    (y : Word (ZMod 2) colTwo) (hy : y ∈ (secondCode D).carrier)
    (hy0 : y ≠ 0) :
    ∃ z : Word (ZMod 2) (QubitIndex rowOne colOne rowTwo colTwo),
      z ∈ (chainComplex D).middleCycleCode.carrier ∧
      z ∉ (chainComplex D).middleBoundaryCode.carrier ∧
      HammingWeight z = HammingWeight x := by sorry
