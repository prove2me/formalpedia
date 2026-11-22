-- Prove2me | Theorems.Thm_P2M_DeciSigma1_Holes_Tail_suffixChain_getElem__eq_of_mem_b81ca86b8910
-- name    : P2M_DeciSigma1_Holes_Tail_suffixChain_getElem__eq_of_mem_b81ca86b8910
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:58:44.788697+00:00
-- url     : https://prove2.me/theorems/cc8810dc-67f8-4b43-afad-64ab75323fdc
-- title:
--   P2 M Deci Sigma1 Holes Tail suffix Chain get Elem  eq of mem b81ca86b8910: P2 M Deci Sigma1 Holes Tail suffix Chain get Elem  eq of mem b81ca86b8910
-- statement:
--   In a suffix chain of `t` with first member `b`, the suffix of length `b` is a prefix of the
--   suffix of length `b'` for every member `b' ≤ |t|`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/WindowChains.lean#L236-L245
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/WindowChains.lean#L236-L245

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Levels
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_WindowChains
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Readers DeciSigma1.Words
variable {α S : Type} {k : ℕ}
variable [DecidableEq α]

theorem P2M_DeciSigma1_Holes_Tail_suffixChain_getElem__eq_of_mem_b81ca86b8910 {t : List α} {b b' : ℕ} {bs : List ℕ}
    (h : SuffixChain t (b :: bs)) (hb' : b' ∈ b :: bs) (hle : b' ≤ t.length) :
    b ≤ b' ∧ ∀ j < b, t[t.length - b' + j]? = t[t.length - b + j]? := by sorry

alias «DeciSigma1».«Holes».«Tail».«suffixChain_getElem?_eq_of_mem» := P2M_DeciSigma1_Holes_Tail_suffixChain_getElem__eq_of_mem_b81ca86b8910
