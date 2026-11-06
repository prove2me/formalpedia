-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_mem_firstTransposeCode_iff
-- name    : QEC.Coding.HypergraphProduct.mem_firstTransposeCode_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:51:39.408934+00:00
-- url     : https://prove2.me/theorems/de0675c5-f953-4395-b8a7-074a14538243
-- title:
--   Hypergraph Product: mem first Transpose Code iff
-- statement:
--   The Hypergraph Product construction uses the mem first Transpose Code iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Parameters.lean#L77-L85
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Parameters.lean#L77-L85

import Definitions.Def_QEC_Coding_HypergraphProduct_Core
import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Mathlib.LinearAlgebra.Matrix.Rank
import Definitions.Def_QEC_Coding_HypergraphProduct_Parameters
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.mem_firstTransposeCode_iff
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    (D : Data F rowOne colOne rowTwo colTwo) (x : Word F rowOne) :
    x ∈ (firstTransposeCode D).carrier ↔
      Matrix.toLin' D.first.transpose x = 0 := by sorry
