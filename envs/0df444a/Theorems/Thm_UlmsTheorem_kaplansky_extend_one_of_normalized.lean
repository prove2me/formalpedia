-- Prove2me | Theorems.Thm_UlmsTheorem_kaplansky_extend_one_of_normalized
-- name    : UlmsTheorem.kaplansky_extend_one_of_normalized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:57:45.379184+00:00
-- url     : https://prove2.me/theorems/70f0063e-1911-448d-b106-261cd9b65f33
-- title:
--   Ulms Theorem: kaplansky extend one of normalized
-- statement:
--   **Kaplansky's one-step extension from an already normalized element.**
--
--   The full `kaplansky_extend_one` theorem below first searches a finite coset for
--   such an `x`.  Once `x` is given with exact height `α`, properness, and the
--   maximal-`p x` normalization, target selection uses the ordinary Ulm invariant
--   only at this single height `α`.  This height-local form is the one needed by
--   the below-base band of the ACM construction, where invariant equality is known
--   only below a cutoff.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L1375-L1406
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L1375-L1406

module
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmInvariants
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Pure
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Extension
set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open Ordinal
universe u
variable (p : ℕ) [hp : Fact p.Prime]
variable {G : Type u} [AddCommGroup G]
variable {H : Type u} [AddCommGroup H]

theorem UlmsTheorem.kaplansky_extend_one_of_normalized
    (hG : IsReducedPGroup p G)
    (s : UlmStage p (G := G) (H := H))
    {x : G} {α : Ordinal.{0}}
    (hinv : ulmInvariant p α (G := G) = ulmInvariant p α (G := H))
    (hx_notin : x ∉ s.A)
    (hpxA : p • x ∈ s.A)
    (hxα : x ∈ ulmSubgroup p α (G := G))
    (hxSucc : x ∉ ulmSubgroup p (Order.succ α) (G := G))
    (hxProper : IsProper p s.A x)
    (hpxMax : ∀ y : G, y - x ∈ s.A → IsProper p s.A y →
      ulmHeight p (p • y) ≤ ulmHeight p (p • x)) :
    ∃ (s' : UlmStage p (G := G) (H := H))
      (hAA : s.A ≤ s'.A) (_hBB : s.B ≤ s'.B),
      x ∈ s'.A ∧
      ∀ a : s.A, (s'.e ⟨a, hAA a.prop⟩ : H) = s.e a := by sorry
