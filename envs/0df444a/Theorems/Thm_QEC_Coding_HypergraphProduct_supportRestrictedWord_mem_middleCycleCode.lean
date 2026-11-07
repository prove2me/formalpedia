-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_supportRestrictedWord_mem_middleCycleCode
-- name    : QEC.Coding.HypergraphProduct.supportRestrictedWord_mem_middleCycleCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:38:13.195028+00:00
-- url     : https://prove2.me/theorems/737ccdac-f262-4b99-b83a-4fa16470a2ad
-- title:
--   Hypergraph Product: support Restricted Word mem middle Cycle Code
-- statement:
--   An original middle cycle restricts to a middle cycle of the support
--   restricted hypergraph product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Embedding.lean#L91-L105
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Embedding.lean#L91-L105

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Restriction
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Embedding
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.supportRestrictedWord_mem_middleCycleCode
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo)
    (z : Word (ZMod 2) (QubitIndex rowOne colOne rowTwo colTwo))
    (hz : z ∈ (chainComplex D).middleCycleCode.carrier) :
    supportRestrictedWord z ∈
      (chainComplex (supportRestrictedData D z)).middleCycleCode.carrier := by sorry
