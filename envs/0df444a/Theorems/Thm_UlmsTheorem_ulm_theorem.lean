-- Prove2me | Theorems.Thm_UlmsTheorem_ulm_theorem
-- name    : UlmsTheorem.ulm_theorem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:58:21.888518+00:00
-- url     : https://prove2.me/theorems/15e4832c-1806-4fad-8081-bf1c73e96f76
-- title:
--   Ulms Theorem: ulm theorem
-- statement:
--   Ulm's theorem: two countable reduced abelian p-groups are isomorphic iff
--   their classical Ulm invariants agree.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Theorem.lean#L53-L61
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Theorem.lean#L53-L61

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

theorem UlmsTheorem.ulm_theorem {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    [Countable G] [Countable H]
    (hGred : IsReducedPGroup p G) (hHred : IsReducedPGroup p H) :
    Nonempty (G ≃+ H) ↔
    ∀ α : Ordinal.{0},
      ulmInvariant p α (G := G) = ulmInvariant p α (G := H) := by sorry
