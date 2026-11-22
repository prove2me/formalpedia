-- Prove2me | Theorems.Thm_UlmsTheorem_IsPure_range_of_heightPresOn
-- name    : UlmsTheorem.IsPure.range_of_heightPresOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:54:28.389527+00:00
-- url     : https://prove2.me/theorems/356c62fb-8a66-4e15-8779-a8fb9da3c686
-- title:
--   Is Pure: range of height Pres On
-- statement:
--   The Is Pure construction uses the range of height Pres On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Pure.lean#L425-L442
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Pure.lean#L425-L442

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

theorem UlmsTheorem.IsPure.range_of_heightPresOn {A : AddSubgroup G} {B : AddSubgroup H}
    (hA : IsPure p A) (φ : A →+ B) (hφ : IsHeightPresOn p φ) :
    IsPure p ((⊤ : AddSubgroup A).map (B.subtype.comp φ)) := by sorry
