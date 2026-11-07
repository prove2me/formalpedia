-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_exists_cohomology_witness_of_first_second_nonzero
-- name    : QEC.Coding.HypergraphProduct.exists_cohomology_witness_of_first_second_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:20:22.278269+00:00
-- url     : https://prove2.me/theorems/5c1ad2ba-56cc-4def-a4a4-a26990e614e7
-- title:
--   Hypergraph Product: exists cohomology witness of first second nonzero
-- statement:
--   A nonzero second-code word has a cohomologically nontrivial first-block
--   representative of the same weight whenever the first code is nonzero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Witness.lean#L480-L512
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Witness.lean#L480-L512

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_LowerBound
import Definitions.Def_QEC_Coding_HypergraphProduct_Locality
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Witness
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.exists_cohomology_witness_of_first_second_nonzero
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
      z ∈ (chainComplex D).middleCocycleCode.carrier ∧
      z ∉ (chainComplex D).firstCoboundaryCheckCode.carrier ∧
      HammingWeight z = HammingWeight y := by sorry
