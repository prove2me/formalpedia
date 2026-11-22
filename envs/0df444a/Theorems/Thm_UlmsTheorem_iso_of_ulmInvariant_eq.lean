-- Prove2me | Theorems.Thm_UlmsTheorem_iso_of_ulmInvariant_eq
-- name    : UlmsTheorem.iso_of_ulmInvariant_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:58:17.452546+00:00
-- url     : https://prove2.me/theorems/f507ef40-c96b-42a8-85e3-8c71de218ab5
-- title:
--   Ulms Theorem: iso of ulm Invariant eq
-- statement:
--   Hard direction of Ulm's theorem: equal Ulm invariants imply isomorphism,
--   using the proved Kaplansky finite-stage extension in both directions.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Classification.lean#L316-L325
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Classification.lean#L316-L325

module
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Extension
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Classification
set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open Ordinal
universe u
variable (p : ℕ) [hp : Fact p.Prime]
variable {G : Type u} [AddCommGroup G]
variable {H : Type u} [AddCommGroup H]

theorem UlmsTheorem.iso_of_ulmInvariant_eq
    [Countable G] [Countable H]
    (hG : IsReducedPGroup p G)
    (hH : IsReducedPGroup p H)
    (hinv : ∀ α : Ordinal.{0},
      ulmInvariant p α (G := G) = ulmInvariant p α (G := H)) :
    Nonempty (G ≃+ H) := by sorry
