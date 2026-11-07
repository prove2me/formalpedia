-- Prove2me | Theorems.Thm_QEC_Coding_SmallSetExpansion_card_filter_product_eq_sum_card_fibers
-- name    : QEC.Coding.SmallSetExpansion.card_filter_product_eq_sum_card_fibers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:47:19.180415+00:00
-- url     : https://prove2.me/theorems/4742d5eb-bb08-4e52-b5b4-f4e892325874
-- title:
--   Small Set Expansion: card filter product eq sum card fibers
-- statement:
--   Count composable pairs by grouping them according to their intermediate
--   value.  This is the finite combinatorial identity behind multiplication of
--   weighted adjacency matrices.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansion.lean#L62-L83
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansion.lean#L62-L83

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}

theorem QEC.Coding.SmallSetExpansion.card_filter_product_eq_sum_card_fibers
    {A B X U : Type*} [Fintype A] [Fintype B] [Fintype X]
    [DecidableEq X] [DecidableEq U]
    (f : A → X) (g : X → B → U) (u : U) :
    (Finset.univ.filter fun p : A × B => g (f p.1) p.2 = u).card =
      ∑ x, (Finset.univ.filter fun a : A => f a = x).card *
        (Finset.univ.filter fun b : B => g x b = u).card := by sorry
