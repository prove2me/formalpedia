-- Prove2me | Theorems.Thm_P2M_BooleanFun_ite_ite_not__7b24d63f550e
-- name    : P2M_BooleanFun_ite_ite_not__7b24d63f550e
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T18:58:57.195714+00:00
-- url     : https://prove2.me/theorems/f5f9ae7f-a750-4904-90e0-eb08d6c798c1
-- title:
--   P2 M Boolean Fun ite ite not  7b24d63f550e: P2 M Boolean Fun ite ite not  7b24d63f550e
-- statement:
--   The P2 M Boolean Fun ite ite not  7b24d63f550e construction uses the P2 M Boolean Fun ite ite not  7b24d63f550e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Auxiliary.lean#L82-L83
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Auxiliary.lean#L82-L83

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
variable {α : Sort*} {P : Prop} [Decidable P] {a b c : α}

theorem P2M_BooleanFun_ite_ite_not__7b24d63f550e(P : Prop) [Decidable P] (a b c : α):
    ite (¬P) (ite P a b) c = ite (¬P) b c := by sorry

alias «BooleanFun».«ite_ite_not'» := P2M_BooleanFun_ite_ite_not__7b24d63f550e
