-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_exists_cohomology_witness_of_transpose_nonzero
-- name    : QEC.Coding.HypergraphProduct.exists_cohomology_witness_of_transpose_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:19:26.919369+00:00
-- url     : https://prove2.me/theorems/2b571f1b-9bf9-4416-9126-0b8fecb35e58
-- title:
--   Hypergraph Product: exists cohomology witness of transpose nonzero
-- statement:
--   A nonzero first-transpose-code word has a cohomologically nontrivial
--   second-block representative of the same weight when the other transpose code
--   is nonzero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Witness.lean#L517-L549
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Witness.lean#L517-L549

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_LowerBound
import Definitions.Def_QEC_Coding_HypergraphProduct_Locality
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Witness
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.exists_cohomology_witness_of_transpose_nonzero
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo)
    (x : Word (ZMod 2) rowOne)
    (hx : x ∈ (firstTransposeCode D).carrier) (hx0 : x ≠ 0)
    (y : Word (ZMod 2) rowTwo)
    (hy : y ∈ (secondTransposeCode D).carrier) (hy0 : y ≠ 0) :
    ∃ z : Word (ZMod 2) (QubitIndex rowOne colOne rowTwo colTwo),
      z ∈ (chainComplex D).middleCocycleCode.carrier ∧
      z ∉ (chainComplex D).firstCoboundaryCheckCode.carrier ∧
      HammingWeight z = HammingWeight x := by sorry
