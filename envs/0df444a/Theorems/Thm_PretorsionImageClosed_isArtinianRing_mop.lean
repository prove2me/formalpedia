-- Prove2me | Theorems.Thm_PretorsionImageClosed_isArtinianRing_mop
-- name    : PretorsionImageClosed.isArtinianRing_mop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:50:58.540865+00:00
-- url     : https://prove2.me/theorems/a4189d33-2244-457d-bade-7f5baa2732ee
-- title:
--   Pretorsion Image Closed: is Artinian Ring mop
-- statement:
--   A finite-dimensional algebra over a field is Artinian, and so is its
--   opposite ring; together with `Statement.isNoetherianRing_mop` this gives the
--   length function on `mod Λ`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Length/Modules.lean#L83-L85
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Length/Modules.lean#L83-L85

module
public import Definitions.Def_PretorsionImageClosed_Length_Basic
public import Definitions.Def_PretorsionImageClosed_Modules_FiniteModules
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Noetherian.Basic
public import Definitions.Def_PretorsionImageClosed_Length_Modules
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits

theorem PretorsionImageClosed.isArtinianRing_mop (k : Type*) [Field k] (Λ : Type*) [Ring Λ] [Algebra k Λ]
    [FiniteDimensional k Λ] : IsArtinianRing Λᵐᵒᵖ := by sorry
