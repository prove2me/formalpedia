-- Prove2me | Theorems.Thm_UlmsTheorem_iso_of_ulm_invariants
-- name    : UlmsTheorem.iso_of_ulm_invariants
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:58:19.645432+00:00
-- url     : https://prove2.me/theorems/de121f30-8ed0-4da5-a730-dd683fa12251
-- title:
--   Ulms Theorem: iso of ulm invariants
-- statement:
--   Public hard direction of Ulm's theorem: equal classical Ulm invariants imply isomorphism
--   for countable reduced abelian `p`-groups.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Theorem.lean#L43-L49
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Theorem.lean#L43-L49

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

theorem UlmsTheorem.iso_of_ulm_invariants {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    [Countable G] [Countable H]
    (hGred : IsReducedPGroup p G) (hHred : IsReducedPGroup p H)
    (hinv : ∀ α : Ordinal.{0},
      ulmInvariant p α (G := G) = ulmInvariant p α (G := H)) :
    Nonempty (G ≃+ H) := by sorry
