-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_binaryCSSCode_xCode
-- name    : QEC.Coding.HypergraphProduct.binaryCSSCode_xCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:02:58.167134+00:00
-- url     : https://prove2.me/theorems/5b978200-a580-4bd4-b72f-d408c43ad984
-- title:
--   Hypergraph Product: binary CSSCode x Code
-- statement:
--   The Hypergraph Product construction uses the binary CSSCode x Code property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Core.lean#L264-L272
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Core.lean#L264-L272

import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_HypergraphProduct_Core
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.binaryCSSCode_xCode
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo) :
    (binaryCSSCode D).xCode = (chainComplex D).firstCoboundaryCheckCode := by sorry

attribute [defeq] QEC.Coding.HypergraphProduct.binaryCSSCode_xCode
