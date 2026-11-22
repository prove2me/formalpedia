-- Prove2me | Theorems.Thm_UlmsTheorem_ulmHeight_subgroup_le_ambient
-- name    : UlmsTheorem.ulmHeight_subgroup_le_ambient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:54:28.841091+00:00
-- url     : https://prove2.me/theorems/b3f30a41-201b-440b-bb99-4e5e17d6f666
-- title:
--   Ulms Theorem: ulm Height subgroup le ambient
-- statement:
--   The Ulms Theorem construction uses the ulm Height subgroup le ambient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Pure.lean#L286-L289
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Pure.lean#L286-L289

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

theorem UlmsTheorem.ulmHeight_subgroup_le_ambient {A : AddSubgroup G} (x : A) :
    ulmHeight p x (G := A) ≤ ulmHeight p (x : G) := by sorry
