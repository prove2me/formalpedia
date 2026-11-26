-- Prove2me | Theorems.Thm_P2M_Finset_card_mulStab_mul_card_image_coe__56c0b835d7e6
-- name    : P2M_Finset_card_mulStab_mul_card_image_coe__56c0b835d7e6
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:56:49.470955+00:00
-- url     : https://prove2.me/theorems/b00c3688-4e14-423e-b948-ec60c3a915d0
-- title:
--   P2 M Finset card mul Stab mul card image coe  56c0b835d7e6: P2 M Finset card mul Stab mul card image coe  56c0b835d7e6
-- statement:
--   A version of Lagrange's theorem.
--
--   Source: https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Erdos338/Kneser/MulStab.lean#L300-L312
-- source:
--   https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Erdos338/Kneser/MulStab.lean#L300-L312

module
public import Mathlib.Algebra.Pointwise.Stabilizer
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.GroupAction.Blocks
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Definitions.Def_Erdos338_Kneser_MulStab
set_option autoImplicit true
@[expose] public section
public section
open Function MulAction
open scoped Pointwise
open Finset
variable {ι α : Type*}
local notation s " +ₛ " N => Finset.image ((↑) : α → α ⧸ N) s
local notation s " +ˢ " N => Set.image ((↑) : α → α ⧸ N) s
variable [CommGroup α] [DecidableEq α] {s t : Finset α} {a : α}

theorem P2M_Finset_card_mulStab_mul_card_image_coe__56c0b835d7e6 (s t : Finset α)
    [DecidableEq (α ⧸ stabilizer α (t : Set α))] :
    #t.mulStab * #(s +ₛ stabilizer α (t : Set α)) = #(s * t.mulStab) := by sorry

alias «Finset».«card_mulStab_mul_card_image_coe'» := P2M_Finset_card_mulStab_mul_card_image_coe__56c0b835d7e6
