-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_exists_nonzero_mem_of_extendedMinimumDistance_ne_top
-- name    : QEC.Coding.HypergraphProduct.exists_nonzero_mem_of_extendedMinimumDistance_ne_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:13:45.61435+00:00
-- url     : https://prove2.me/theorems/21d94594-e201-4a07-863c-22982a7b1ad6
-- title:
--   Hypergraph Product: exists nonzero mem of extended Minimum Distance ne top
-- statement:
--   The Hypergraph Product construction uses the exists nonzero mem of extended Minimum Distance ne top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/UpperBound.lean#L18-L28
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance/UpperBound.lean#L18-L28

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Witness
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_UpperBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.exists_nonzero_mem_of_extendedMinimumDistance_ne_top
    {F : Type v} {A : Type u}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype A] [DecidableEq A]
    (C : LinearCode F A) (hFinite : extendedMinimumDistance C ≠ ⊤) :
    ∃ x, x ∈ C.carrier ∧ x ≠ 0 := by sorry
