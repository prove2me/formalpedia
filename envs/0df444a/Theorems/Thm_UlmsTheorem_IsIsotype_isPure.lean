-- Prove2me | Theorems.Thm_UlmsTheorem_IsIsotype_isPure
-- name    : UlmsTheorem.IsIsotype.isPure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:54:26.273174+00:00
-- url     : https://prove2.me/theorems/ffc52f61-baaa-4b60-b01c-1566bfa50aa3
-- title:
--   Is Isotype: is Pure
-- statement:
--   The Is Isotype construction uses the is Pure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Pure.lean#L279-L284
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Pure.lean#L279-L284

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

theorem UlmsTheorem.IsIsotype.isPure {A : AddSubgroup G} (hA : IsIsotype p A) :
    IsPure p A := by sorry
