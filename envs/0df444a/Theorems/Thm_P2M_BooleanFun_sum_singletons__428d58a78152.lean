-- Prove2me | Theorems.Thm_P2M_BooleanFun_sum_singletons__428d58a78152
-- name    : P2M_BooleanFun_sum_singletons__428d58a78152
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T18:58:37.37875+00:00
-- url     : https://prove2.me/theorems/b4192924-dac5-4fe6-ab56-37f1e0faef13
-- title:
--   P2 M Boolean Fun sum singletons  428d58a78152: P2 M Boolean Fun sum singletons  428d58a78152
-- statement:
--   The P2 M Boolean Fun sum singletons  428d58a78152 construction uses the P2 M Boolean Fun sum singletons  428d58a78152 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Auxiliary.lean#L57-L58
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Auxiliary.lean#L57-L58

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Real.Sqrt
import Definitions.Def_BooleanFun_Auxiliary
set_option autoImplicit false
open BooleanFun
open Finset Pi
variable {α : Type*} {β : Type*}
variable {s : Finset α}
variable {ι : Type*} [Fintype ι]
variable {κ : Type*}
variable {R : Type*} {M : Type*}
variable [Ring R] [AddCommGroup M] [Module R M]

theorem P2M_BooleanFun_sum_singletons__428d58a78152 [AddCommMonoid α] {F : Finset ι → α}:
    ∑ S ∈ {S|S.card = 1}, F S = ∑ i, F {i} := by sorry

alias «BooleanFun».«sum_singletons'» := P2M_BooleanFun_sum_singletons__428d58a78152
