-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_secondTransposeCode_transposeData
-- name    : QEC.Coding.HypergraphProduct.secondTransposeCode_transposeData
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:33:51.342063+00:00
-- url     : https://prove2.me/theorems/0a63d9a9-4717-4f48-9145-fafa13ac9d68
-- title:
--   Hypergraph Product: second Transpose Code transpose Data
-- statement:
--   The Hypergraph Product construction uses the second Transpose Code transpose Data property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Duality.lean#L84-L91
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Duality.lean#L84-L91

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Embedding
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Duality
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.secondTransposeCode_transposeData
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo) :
    secondTransposeCode (transposeData D) = secondCode D := by sorry

attribute [defeq] QEC.Coding.HypergraphProduct.secondTransposeCode_transposeData
