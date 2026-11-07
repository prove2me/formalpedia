-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_mem_middleBoundaryCode_of_supportRestrictedWord_mem
-- name    : QEC.Coding.HypergraphProduct.mem_middleBoundaryCode_of_supportRestrictedWord_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:38:39.218134+00:00
-- url     : https://prove2.me/theorems/b5c579f6-a33a-4db3-909d-1491bc237984
-- title:
--   Hypergraph Product: mem middle Boundary Code of support Restricted Word mem
-- statement:
--   Membership in the restricted boundary code implies membership of the
--   original supported word in the original boundary code.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Embedding.lean#L228-L244
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Embedding.lean#L228-L244

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Restriction
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Embedding
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.mem_middleBoundaryCode_of_supportRestrictedWord_mem
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo)
    (z : Word (ZMod 2) (QubitIndex rowOne colOne rowTwo colTwo))
    (hz : supportRestrictedWord z ∈
      (chainComplex (supportRestrictedData D z)).middleBoundaryCode.carrier) :
    z ∈ (chainComplex D).middleBoundaryCode.carrier := by sorry
