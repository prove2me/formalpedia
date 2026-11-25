-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_eq_scalarHom_comp_canonicalHom
-- name    : PretorsionImageClosed.LinearQuiver.eq_scalarHom_comp_canonicalHom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:08:40.838324+00:00
-- url     : https://prove2.me/theorems/95e484b3-3a88-4ae9-957a-e63179f7fc63
-- title:
--   Linear Quiver: eq scalar Hom comp canonical Hom
-- statement:
--   Proposition 5.2: a morphism `M_{c,d} ⟶ M_{a,b}` is a scalar times the
--   canonical morphism.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Subobjects.lean#L77-L87
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Subobjects.lean#L77-L87

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Indecomposables
public import Definitions.Def_PretorsionImageClosed_Subcategories_Trace
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Subobjects
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement
open PretorsionImageClosed.LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}

theorem PretorsionImageClosed.LinearQuiver.eq_scalarHom_comp_canonicalHom {c d a b : Fin n} (η : interval k c d ⟶ interval k a b)
    (hac : a ≤ c) (hbd : b ≤ d) :
    η = scalarHom c d (coord η c) ≫ canonicalHom hac hbd := by sorry
