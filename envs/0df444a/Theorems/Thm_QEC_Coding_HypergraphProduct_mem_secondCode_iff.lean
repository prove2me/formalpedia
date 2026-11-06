-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_mem_secondCode_iff
-- name    : QEC.Coding.HypergraphProduct.mem_secondCode_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:51:35.390914+00:00
-- url     : https://prove2.me/theorems/a4d75909-5755-4d97-b374-65fb09a29192
-- title:
--   Hypergraph Product: mem second Code iff
-- statement:
--   The Hypergraph Product construction uses the mem second Code iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Parameters.lean#L67-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Parameters.lean#L67-L74

import Definitions.Def_QEC_Coding_HypergraphProduct_Core
import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Mathlib.LinearAlgebra.Matrix.Rank
import Definitions.Def_QEC_Coding_HypergraphProduct_Parameters
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.mem_secondCode_iff
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo) (x : Word F colTwo) :
    x ∈ (secondCode D).carrier ↔ Matrix.toLin' D.second x = 0 := by sorry
