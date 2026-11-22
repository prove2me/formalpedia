-- Prove2me | Theorems.Thm_UlmsTheorem_markedGradedToHill_surjective
-- name    : UlmsTheorem.markedGradedToHill_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:58:00.469735+00:00
-- url     : https://prove2.me/theorems/d1bf6c04-9ad6-48bb-b52a-c6aaae4b8e94
-- title:
--   Ulms Theorem: marked Graded To Hill surjective
-- statement:
--   The Ulms Theorem construction uses the marked Graded To Hill surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/UlmInvariants.lean#L301-L303
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/UlmInvariants.lean#L301-L303

module
public import Mathlib.Algebra.Field.ZMod
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Socle
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Heights
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmInvariants
set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open Ordinal Cardinal
variable (p : ℕ) [hp : Fact p.Prime]
variable {G : Type*} [AddCommGroup G]

theorem UlmsTheorem.markedGradedToHill_surjective (S : AddSubgroup G) (α : Ordinal) :
    Function.Surjective (markedGradedToHill (p := p) S α) := by sorry
