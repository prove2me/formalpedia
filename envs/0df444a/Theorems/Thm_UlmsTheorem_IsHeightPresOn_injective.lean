-- Prove2me | Theorems.Thm_UlmsTheorem_IsHeightPresOn_injective
-- name    : UlmsTheorem.IsHeightPresOn.injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:54:08.718036+00:00
-- url     : https://prove2.me/theorems/078ded96-b137-49ee-8d91-1859027a26e7
-- title:
--   Is Height Pres On: injective
-- statement:
--   The Is Height Pres On construction uses the injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Pure.lean#L307-L316
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Pure.lean#L307-L316

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

theorem UlmsTheorem.IsHeightPresOn.injective (hred : IsPReduced p G)
    {A : AddSubgroup G} {B : AddSubgroup H} {φ : A →+ B} (hφ : IsHeightPresOn p φ) :
    Function.Injective φ := by sorry
