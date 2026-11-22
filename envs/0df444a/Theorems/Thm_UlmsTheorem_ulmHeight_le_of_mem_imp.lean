-- Prove2me | Theorems.Thm_UlmsTheorem_ulmHeight_le_of_mem_imp
-- name    : UlmsTheorem.ulmHeight_le_of_mem_imp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:54:09.663323+00:00
-- url     : https://prove2.me/theorems/ac783f82-8023-4871-9eba-ce27b0b62f17
-- title:
--   Ulms Theorem: ulm Height le of mem imp
-- statement:
--   Filtration-membership domination implies domination of ordinal Ulm heights.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Pure.lean#L44-L48
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Pure.lean#L44-L48

module
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Heights
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Tactic.NormNum.GCD
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Pure
set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open Ordinal
universe u
variable (p : ℕ)
variable {G : Type u} [AddCommGroup G]
variable {H : Type u} [AddCommGroup H]

theorem UlmsTheorem.ulmHeight_le_of_mem_imp (x y : G)
    (h : ∀ α : Ordinal.{0},
      x ∈ ulmSubgroup p α (G := G) → y ∈ ulmSubgroup p α (G := G)) :
    ulmHeight p x ≤ ulmHeight p y := by sorry
