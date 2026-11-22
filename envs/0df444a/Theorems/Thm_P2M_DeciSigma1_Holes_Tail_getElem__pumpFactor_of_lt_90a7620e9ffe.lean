-- Prove2me | Theorems.Thm_P2M_DeciSigma1_Holes_Tail_getElem__pumpFactor_of_lt_90a7620e9ffe
-- name    : P2M_DeciSigma1_Holes_Tail_getElem__pumpFactor_of_lt_90a7620e9ffe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:49:09.070145+00:00
-- url     : https://prove2.me/theorems/aefb462a-11c2-44d1-9edc-8338ea85b131
-- title:
--   P2 M Deci Sigma1 Holes Tail get Elem  pump Factor of lt 90a7620e9ffe: P2 M Deci Sigma1 Holes Tail get Elem  pump Factor of lt 90a7620e9ffe
-- statement:
--   The P2 M Deci Sigma1 Holes Tail get Elem  pump Factor of lt 90a7620e9ffe construction uses the P2 M Deci Sigma1 Holes Tail get Elem  pump Factor of lt 90a7620e9ffe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L534-L540
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L534-L540

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_DifferenceConstraints
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_SuffixChains
public import Mathlib.Order.Nat
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Rays
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Readers
open DeciSigma1.Words (pow)
open DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
variable {x : List α} {c c' L : ℕ}

theorem P2M_DeciSigma1_Holes_Tail_getElem__pumpFactor_of_lt_90a7620e9ffe (hcc : c < c') (hc' : c' ≤ x.length) (hL : c' - c ≤ L) {p : ℕ}
    (hp : p < c') : (pumpFactor x c c' L)[p]? = x[p]? := by sorry

alias «DeciSigma1».«Holes».«Tail».«getElem?_pumpFactor_of_lt» := P2M_DeciSigma1_Holes_Tail_getElem__pumpFactor_of_lt_90a7620e9ffe
