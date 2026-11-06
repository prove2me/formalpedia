-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_mem_firstCode_iff
-- name    : QEC.Coding.HypergraphProduct.mem_firstCode_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:51:14.700311+00:00
-- url     : https://prove2.me/theorems/b9da4a01-5743-4906-a109-4f0977573660
-- title:
--   Hypergraph Product: mem first Code iff
-- statement:
--   The Hypergraph Product construction uses the mem first Code iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Parameters.lean#L57-L64
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Parameters.lean#L57-L64

import Definitions.Def_QEC_Coding_HypergraphProduct_Core
import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Mathlib.LinearAlgebra.Matrix.Rank
import Definitions.Def_QEC_Coding_HypergraphProduct_Parameters
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.mem_firstCode_iff
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    (D : Data F rowOne colOne rowTwo colTwo) (x : Word F colOne) :
    x ∈ (firstCode D).carrier ↔ Matrix.toLin' D.first x = 0 := by sorry
