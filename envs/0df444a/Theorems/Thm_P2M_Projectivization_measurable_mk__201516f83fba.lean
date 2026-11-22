-- Prove2me | Theorems.Thm_P2M_Projectivization_measurable_mk__201516f83fba
-- name    : P2M_Projectivization_measurable_mk__201516f83fba
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:52:11.980429+00:00
-- url     : https://prove2.me/theorems/05b7ce31-6dc3-49c8-9bec-baba0c8e433a
-- title:
--   P2 M Projectivization measurable mk  201516f83fba: P2 M Projectivization measurable mk  201516f83fba
-- statement:
--   The canonical surjection `{v : V // v ≠ 0} → ℙ K V` is measurable.
--   Follows from continuity (`Topology.lean`'s `continuous_mk'`) via
--   `Continuous.measurable`.
--
--   Stated under additional `[MeasurableSpace V] [BorelSpace V]` hypotheses
--   so the source subtype `{v : V // v ≠ 0}` inherits a Borel `MeasurableSpace`
--   via `Subtype.borelSpace`. Most callers will supply these (typically via
--   `borelize V`); the resulting `MeasurableSpace V` agrees with `borel V`.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/LinearAlgebra/Projectivization/MeasureSpace.lean#L73-L75
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/LinearAlgebra/Projectivization/MeasureSpace.lean#L73-L75

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
omit [FiniteDimensional K V]

theorem P2M_Projectivization_measurable_mk__201516f83fba [MeasurableSpace V] [BorelSpace V] :
    Measurable (mk' K : { v : V // v ≠ 0 } → ℙ K V) := by sorry

alias «Projectivization».«measurable_mk'» := P2M_Projectivization_measurable_mk__201516f83fba
