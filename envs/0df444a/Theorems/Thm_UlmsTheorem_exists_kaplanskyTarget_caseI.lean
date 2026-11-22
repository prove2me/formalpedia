-- Prove2me | Theorems.Thm_UlmsTheorem_exists_kaplanskyTarget_caseI
-- name    : UlmsTheorem.exists_kaplanskyTarget_caseI
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:57:46.602725+00:00
-- url     : https://prove2.me/theorems/fa304b2a-70cc-4625-9b56-71bf393fe5da
-- title:
--   Ulms Theorem: exists kaplansky Target case I
-- statement:
--   Kaplansky's Case I target construction.
--
--   If `p • x` has exact height `α+1`, any height-`α` root of its image is
--   automatically proper over the target stage.  The proof uses the second
--   normalization of `x` to rule out a higher translate.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L1234-L1302
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L1234-L1302

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
omit hp

theorem UlmsTheorem.exists_kaplanskyTarget_caseI
    {α : Ordinal.{0}} (s : UlmStageAt p (G := G) (H := H) α)
    {x : G}
    (hpxA : p • x ∈ s.A)
    (hxα : x ∈ ulmSubgroup p α (G := G))
    (hxSucc : x ∉ ulmSubgroup p (Order.succ α) (G := G))
    (hxProper : IsProper p s.A x)
    (hpxMax : ∀ y : G, y - x ∈ s.A → IsProper p s.A y →
      ulmHeight p (p • y) ≤ ulmHeight p (p • x))
    (hcaseI :
      p • x ∉ ulmSubgroup p (Order.succ (Order.succ α)) (G := G)) :
    ∃ w : H,
      p • w = (s.e ⟨p • x, hpxA⟩ : H) ∧
      w ∈ ulmSubgroup p α (G := H) ∧
      w ∉ ulmSubgroup p (Order.succ α) (G := H) ∧
      IsProper p s.B w := by sorry
