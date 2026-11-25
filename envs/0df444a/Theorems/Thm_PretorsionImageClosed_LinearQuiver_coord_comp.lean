-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_coord_comp
-- name    : PretorsionImageClosed.LinearQuiver.coord_comp
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:28:01.241276+00:00
-- url     : https://prove2.me/theorems/29bea5d5-8db3-41b2-b272-237a450ca1ce
-- title:
--   Linear Quiver: coord comp
-- statement:
--   The Linear Quiver construction uses the coord comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Indecomposables.lean#L38-L45
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Indecomposables.lean#L38-L45

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Decomposition
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Indecomposables
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits
open PretorsionImageClosed.LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}

theorem PretorsionImageClosed.LinearQuiver.coord_comp {c d a b a' b' : Fin n} (η : interval k c d ⟶ interval k a b)
    (θ : interval k a b ⟶ interval k a' b') (i : Fin n) :
    coord (η ≫ θ) i = coord η i * coord θ i := by sorry
