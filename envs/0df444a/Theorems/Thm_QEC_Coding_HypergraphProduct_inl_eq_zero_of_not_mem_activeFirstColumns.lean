-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_inl_eq_zero_of_not_mem_activeFirstColumns
-- name    : QEC.Coding.HypergraphProduct.inl_eq_zero_of_not_mem_activeFirstColumns
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:29:35.0063+00:00
-- url     : https://prove2.me/theorems/a071ebd3-22a7-492d-9d10-1c13262b352c
-- title:
--   Hypergraph Product: inl eq zero of not mem active First Columns
-- statement:
--   The Hypergraph Product construction uses the inl eq zero of not mem active First Columns property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Restriction.lean#L86-L99
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Restriction.lean#L86-L99

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Support
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Restriction
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.inl_eq_zero_of_not_mem_activeFirstColumns
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Zero F] [DecidableEq F]
    [Fintype rowOne] [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [Fintype colTwo]
    (z : Word F (QubitIndex rowOne colOne rowTwo colTwo))
    {c₁ : colOne} (hc₁ : c₁ ∉ activeFirstColumns z) (c₂ : colTwo) :
    z (Sum.inl (c₁, c₂)) = 0 := by sorry
