-- Prove2me | Theorems.Thm_P2M_Projectivization_measurable_iff_measurable_comp_mk__5d5b7c48e6fb
-- name    : P2M_Projectivization_measurable_iff_measurable_comp_mk__5d5b7c48e6fb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:52:21.438362+00:00
-- url     : https://prove2.me/theorems/7ea3b0bc-f31f-4947-815b-32eb3d57cff9
-- title:
--   P2 M Projectivization measurable iff measurable comp mk  5d5b7c48e6fb: P2 M Projectivization measurable iff measurable comp mk  5d5b7c48e6fb
-- statement:
--   A function out of `ℙ K V` is measurable iff its precomposition with
--   `mk'` is measurable.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/LinearAlgebra/Projectivization/MeasureSpace.lean#L118-L133
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/LinearAlgebra/Projectivization/MeasureSpace.lean#L118-L133

module
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_Topology
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_MeasureSpace
set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory Topology
open scoped LinearAlgebra.Projectivization
open Projectivization
variable {K V : Type*}
variable [RCLike K] [NormedAddCommGroup V] [NormedSpace K V] [FiniteDimensional K V]

theorem P2M_Projectivization_measurable_iff_measurable_comp_mk__5d5b7c48e6fb [MeasurableSpace V] [BorelSpace V]
    {α : Type*} [MeasurableSpace α] (g : ℙ K V → α) :
    Measurable g ↔ Measurable (g ∘ (mk' K : _ → ℙ K V)) := by sorry

alias «Projectivization».«measurable_iff_measurable_comp_mk'» := P2M_Projectivization_measurable_iff_measurable_comp_mk__5d5b7c48e6fb
