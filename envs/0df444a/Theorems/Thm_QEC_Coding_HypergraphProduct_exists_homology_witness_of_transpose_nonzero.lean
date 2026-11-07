-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_exists_homology_witness_of_transpose_nonzero
-- name    : QEC.Coding.HypergraphProduct.exists_homology_witness_of_transpose_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:22:33.656197+00:00
-- url     : https://prove2.me/theorems/a44a579c-cf10-45bf-af95-c6f8863d60ef
-- title:
--   Hypergraph Product: exists homology witness of transpose nonzero
-- statement:
--   A nonzero second-transpose-code word has a homologically nontrivial
--   second-block representative of the same weight when the other transpose code
--   is nonzero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Witness.lean#L554-L586
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Witness.lean#L554-L586

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_LowerBound
import Definitions.Def_QEC_Coding_HypergraphProduct_Locality
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Witness
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.exists_homology_witness_of_transpose_nonzero
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
      z ∈ (chainComplex D).middleCycleCode.carrier ∧
      z ∉ (chainComplex D).middleBoundaryCode.carrier ∧
      HammingWeight z = HammingWeight y := by sorry
