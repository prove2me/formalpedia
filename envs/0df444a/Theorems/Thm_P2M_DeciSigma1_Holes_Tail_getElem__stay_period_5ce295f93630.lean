-- Prove2me | Theorems.Thm_P2M_DeciSigma1_Holes_Tail_getElem__stay_period_5ce295f93630
-- name    : P2M_DeciSigma1_Holes_Tail_getElem__stay_period_5ce295f93630
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:56:56.50559+00:00
-- url     : https://prove2.me/theorems/974c144d-153c-40bb-9d93-a0ea1bc2fe2f
-- title:
--   P2 M Deci Sigma1 Holes Tail get Elem  stay period 5ce295f93630: P2 M Deci Sigma1 Holes Tail get Elem  stay period 5ce295f93630
-- statement:
--   The P2 M Deci Sigma1 Holes Tail get Elem  stay period 5ce295f93630 construction uses the P2 M Deci Sigma1 Holes Tail get Elem  stay period 5ce295f93630 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L542-L547
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L542-L547

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

theorem P2M_DeciSigma1_Holes_Tail_getElem__stay_period_5ce295f93630 (hcc : c < c') (hc' : c' ≤ x.length) {p : ℕ} (hc : c ≤ p)
    (hp : p + (c' - c) < c + L) :
    (pumpFactor x c c' L)[p + (c' - c)]? = (pumpFactor x c c' L)[p]? := by sorry

alias «DeciSigma1».«Holes».«Tail».«getElem?_stay_period» := P2M_DeciSigma1_Holes_Tail_getElem__stay_period_5ce295f93630
