-- Prove2me | Theorems.Thm_PretorsionImageClosed_IndecomposableSkeleton_mem_qClosure_iff_inFac
-- name    : PretorsionImageClosed.IndecomposableSkeleton.mem_qClosure_iff_inFac
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T00:48:25.325627+00:00
-- url     : https://prove2.me/theorems/d8066f34-ff96-4446-8135-f36991a7af40
-- title:
--   Indecomposable Skeleton: mem q Closure iff in Fac
-- statement:
--   Membership in the quotient closure, unfolded to its presentation.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ModuleTraces.lean#L550-L552
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/ModuleTraces.lean#L550-L552

module
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Order.CompactlyGenerated.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Presentations
public import Definitions.Def_PretorsionImageClosed_Modules_FiniteModules
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ModuleTraces
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Set
open CategoryTheory CategoryTheory.Limits
open PretorsionImageClosed PretorsionImageClosed.IndecomposableSkeleton
universe u v w
variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)
attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

theorem PretorsionImageClosed.IndecomposableSkeleton.mem_qClosure_iff_inFac (S : Set ι) (j : ι) :
    j ∈ σ.qClosure S ↔ σ.InFac S (σ.obj j) := by sorry
