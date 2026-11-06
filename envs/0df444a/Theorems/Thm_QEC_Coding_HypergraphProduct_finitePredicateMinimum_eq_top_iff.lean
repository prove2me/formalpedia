-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_finitePredicateMinimum_eq_top_iff
-- name    : QEC.Coding.HypergraphProduct.finitePredicateMinimum_eq_top_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:52:26.937135+00:00
-- url     : https://prove2.me/theorems/a749ed21-ac8c-462d-9229-6d4f055bc9ab
-- title:
--   Hypergraph Product: finite Predicate Minimum eq top iff
-- statement:
--   The Hypergraph Product construction uses the finite Predicate Minimum eq top iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance.lean#L46-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance.lean#L46-L59

import Definitions.Def_QEC_Coding_HypergraphProduct_Parameters
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v

theorem QEC.Coding.HypergraphProduct.finitePredicateMinimum_eq_top_iff
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    {P : alpha → Prop} [DecidablePred P] {weight : alpha → Nat} :
    finitePredicateMinimum P weight = ⊤ ↔ ∀ x, ¬ P x := by sorry
