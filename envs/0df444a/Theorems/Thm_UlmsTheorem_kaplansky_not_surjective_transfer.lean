-- Prove2me | Theorems.Thm_UlmsTheorem_kaplansky_not_surjective_transfer
-- name    : UlmsTheorem.kaplansky_not_surjective_transfer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:57:28.137726+00:00
-- url     : https://prove2.me/theorems/ec8c024c-e21c-423c-a369-3d11f44101b7
-- title:
--   Ulms Theorem: kaplansky not surjective transfer
-- statement:
--   Non-surjectivity of Kaplansky's range map transfers across a finite
--   height-preserving stage when the ordinary Ulm invariants at `α` agree.
--
--   Finiteness of the source quotient is essential here: injective endomorphisms
--   of infinite-dimensional spaces need not be onto.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L669-L718
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L669-L718

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

theorem UlmsTheorem.kaplansky_not_surjective_transfer
    {α : Ordinal.{0}} (s : UlmStageAt p (G := G) (H := H) α)
    (hinv :
      ulmInvariant p α (G := G) = ulmInvariant p α (G := H))
    (hGroom : ¬ Function.Surjective (kaplanskyMap p s.A α)) :
    ¬ Function.Surjective (kaplanskyMap p s.B α) := by sorry
