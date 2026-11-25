-- Prove2me | Theorems.Thm_PretorsionImageClosed_FiniteLengthDecomposition_exists_biproduct_decomposition
-- name    : PretorsionImageClosed.FiniteLengthDecomposition.exists_biproduct_decomposition
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T04:38:15.128248+00:00
-- url     : https://prove2.me/theorems/7683ad74-bd24-5df6-ad20-6d424dc87e53
-- title:
--   Finite Length Decomposition: exists biproduct decomposition
-- statement:
--   The finite-length decomposition theorem in categorical biproduct form.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/Decomposition.lean#L188-L195
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/Decomposition.lean#L188-L195

module
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.CategoryTheory.FintypeCat
public import Mathlib.RingTheory.Length
public import Mathlib.Tactic.Ring
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Skeleton
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Decomposition
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
open PretorsionImageClosed PretorsionImageClosed.FiniteLengthDecomposition
universe u w
variable {R : Type u} [Ring R] [IsNoetherianRing R]
attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

theorem PretorsionImageClosed.FiniteLengthDecomposition.exists_biproduct_decomposition
    (X : FGModuleCat.{w} R) (hfinite : IsFiniteLength R X) :
    ∃ (J : FintypeCat.{0}) (Y : J → FGModuleCat.{w} R),
      (∀ j, PretorsionImageClosed.IsIndecomposableModule R (Y j)) ∧
      Nonempty (X ≅ biproduct Y) := by sorry
