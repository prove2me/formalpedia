-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_inr_eq_zero_of_not_mem_activeSecondRows
-- name    : QEC.Coding.HypergraphProduct.inr_eq_zero_of_not_mem_activeSecondRows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:29:43.73594+00:00
-- url     : https://prove2.me/theorems/ddb170cb-2590-4134-afe1-62e354faca28
-- title:
--   Hypergraph Product: inr eq zero of not mem active Second Rows
-- statement:
--   The Hypergraph Product construction uses the inr eq zero of not mem active Second Rows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Restriction.lean#L101-L114
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/Restriction.lean#L101-L114

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Support
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Restriction
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.inr_eq_zero_of_not_mem_activeSecondRows
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Zero F] [DecidableEq F]
    [Fintype rowOne] [Fintype colOne]
    [Fintype rowTwo] [DecidableEq rowTwo] [Fintype colTwo]
    (z : Word F (QubitIndex rowOne colOne rowTwo colTwo))
    (r₁ : rowOne) {r₂ : rowTwo} (hr₂ : r₂ ∉ activeSecondRows z) :
    z (Sum.inr (r₁, r₂)) = 0 := by sorry
