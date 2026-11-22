-- Prove2me | Theorems.Thm_UlmsTheorem_IsPure_map_of_heightPres
-- name    : UlmsTheorem.IsPure.map_of_heightPres
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:54:29.888353+00:00
-- url     : https://prove2.me/theorems/d22ed2dd-37d5-4cac-969b-e30e3855f988
-- title:
--   Is Pure: map of height Pres
-- statement:
--   The Is Pure construction uses the map of height Pres property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Pure.lean#L407-L423
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Pure.lean#L407-L423

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

theorem UlmsTheorem.IsPure.map_of_heightPres {A : AddSubgroup G} (hA : IsPure p A)
    (φ : G →+ H) (hφ : IsHeightPreserving p φ) :
    IsPure p (A.map φ) := by sorry
