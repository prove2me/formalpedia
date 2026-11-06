-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_chainComplex_boundary1
-- name    : QEC.Coding.HypergraphProduct.chainComplex_boundary1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:03:03.233378+00:00
-- url     : https://prove2.me/theorems/db5910a8-6daf-45a0-97f0-d03f90137274
-- title:
--   Hypergraph Product: chain Complex boundary1
-- statement:
--   The Hypergraph Product construction uses the chain Complex boundary1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Core.lean#L227-L236
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Core.lean#L227-L236

import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_HypergraphProduct_Core
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.chainComplex_boundary1
    {F : Type u} {rowOne colOne rowTwo colTwo : Type v}
    [Field F] [Fintype F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo) :
    (chainComplex D).boundary1 = boundary1 D := by sorry

attribute [defeq] QEC.Coding.HypergraphProduct.chainComplex_boundary1
