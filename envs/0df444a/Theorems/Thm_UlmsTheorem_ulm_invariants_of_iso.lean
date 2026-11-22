-- Prove2me | Theorems.Thm_UlmsTheorem_ulm_invariants_of_iso
-- name    : UlmsTheorem.ulm_invariants_of_iso
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:58:16.718675+00:00
-- url     : https://prove2.me/theorems/c26cb897-030e-4e64-a7fd-34e34512ca42
-- title:
--   Ulms Theorem: ulm invariants of iso
-- statement:
--   Public easy direction of Ulm's theorem: an isomorphism preserves all
--   classical Ulm invariants.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Theorem.lean#L33-L39
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Theorem.lean#L33-L39

module
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmInvariants
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Classification
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Invariance
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Theorem
set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open Cardinal Ordinal
universe u
variable (p : ℕ) [hp : Fact p.Prime]

theorem UlmsTheorem.ulm_invariants_of_iso {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    (hiso : Nonempty (G ≃+ H)) :
    ∀ α : Ordinal.{0},
      ulmInvariant p α (G := G) = ulmInvariant p α (G := H) := by sorry
