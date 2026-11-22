-- Prove2me | Theorems.Thm_P2M_DeciSigma1_Holes_Tail_getElem__pumpFactor_ge_c1284156d4c1
-- name    : P2M_DeciSigma1_Holes_Tail_getElem__pumpFactor_ge_c1284156d4c1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:56:50.193085+00:00
-- url     : https://prove2.me/theorems/b03e03cc-dd96-4142-9864-5e5a44bae3c5
-- title:
--   P2 M Deci Sigma1 Holes Tail get Elem  pump Factor ge c1284156d4c1: P2 M Deci Sigma1 Holes Tail get Elem  pump Factor ge c1284156d4c1
-- statement:
--   The letters of the periodic part of a pumped factor.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L524-L532
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L524-L532

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

theorem P2M_DeciSigma1_Holes_Tail_getElem__pumpFactor_ge_c1284156d4c1 (hcc : c < c') (hc' : c' ≤ x.length) {p : ℕ} (hc : c ≤ p)
    (hp : p < c + L) : (pumpFactor x c c' L)[p]? = x[c + (p - c) % (c' - c)]? := by sorry

alias «DeciSigma1».«Holes».«Tail».«getElem?_pumpFactor_ge» := P2M_DeciSigma1_Holes_Tail_getElem__pumpFactor_ge_c1284156d4c1
