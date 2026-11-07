-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_firstCode_transposeData
-- name    : QEC.Coding.HypergraphProduct.firstCode_transposeData
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:33:05.21322+00:00
-- url     : https://prove2.me/theorems/4c6c6208-30b1-4c93-a0ec-57a37118da73
-- title:
--   Hypergraph Product: first Code transpose Data
-- statement:
--   The Hypergraph Product construction uses the first Code transpose Data property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Duality.lean#L75-L81
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Duality.lean#L75-L81

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Embedding
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Duality
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.firstCode_transposeData
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    (D : Data F rowOne colOne rowTwo colTwo) :
    firstCode (transposeData D) = firstTransposeCode D := by sorry

attribute [defeq] QEC.Coding.HypergraphProduct.firstCode_transposeData
