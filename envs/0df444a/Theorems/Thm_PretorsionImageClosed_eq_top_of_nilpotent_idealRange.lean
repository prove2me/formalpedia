-- Prove2me | Theorems.Thm_PretorsionImageClosed_eq_top_of_nilpotent_idealRange
-- name    : PretorsionImageClosed.eq_top_of_nilpotent_idealRange
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T05:10:29.399647+00:00
-- url     : https://prove2.me/theorems/eda7b13f-5c44-4e83-b925-735c05747ccf
-- title:
--   Pretorsion Image Closed: eq top of nilpotent ideal Range
-- statement:
--   Nilpotence of an ideal, together with a fully invariant submodule
--   and generation modulo that submodule by the ideal's images, forces the
--   submodule to be the whole module.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/EndomorphismRadical.lean#L244-L275
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/EndomorphismRadical.lean#L244-L275

module
public import Mathlib.RingTheory.Artinian.Ring
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ModuleTraces
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_EndomorphismRadical
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Function
open PretorsionImageClosed
universe u v
variable {A : Type u} {X : Type v}
variable [Ring A] [AddCommGroup X] [Module A X]

theorem PretorsionImageClosed.eq_top_of_nilpotent_idealRange
    (I : Ideal (Module.End A X)) [I.IsTwoSided]
    (T : Submodule A X)
    (hT : ∀ f : Module.End A X, Submodule.map f T ≤ T)
    (hI : IsNilpotent I)
    (hsup : T ⊔ idealRange I = ⊤) :
    T = ⊤ := by sorry
