-- Prove2me | Theorems.Thm_P2M_Projectivization_borel_eq_map_mk__60a95bc3fc91
-- name    : P2M_Projectivization_borel_eq_map_mk__60a95bc3fc91
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:52:09.769983+00:00
-- url     : https://prove2.me/theorems/faf520ed-77e8-40ea-876c-1045806176b1
-- title:
--   P2 M Projectivization borel eq map mk  60a95bc3fc91: P2 M Projectivization borel eq map mk  60a95bc3fc91
-- statement:
--   The Borel σ-algebra on `ℙ K V` coincides with the σ-algebra
--   coinduced from the Borel σ-algebra on `{v : V // v ≠ 0}` via `mk'`.
--
--   It lets `measurable_iff_measurable_comp_mk'` (below) reduce measurability of
--   a function on `ℙ K V` (against the Borel σ-algebra) to measurability of its
--   composition with `mk'` (against the Borel σ-algebra on the nonzero subtype).
--
--   `V` is Polish under our hypotheses (`ProperSpace V` via
--   `FiniteDimensional.proper_rclike` gives second-countable + complete +
--   metrizable, hence Polish via the `Mathlib.Topology.MetricSpace.Polish`
--   `PolishSpace` instance for separable + completely metrizable). The
--   nonzero subtype is open in `V`, hence also Polish via
--   `IsOpen.polishSpace`.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/LinearAlgebra/Projectivization/MeasureSpace.lean#L104-L112
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/LinearAlgebra/Projectivization/MeasureSpace.lean#L104-L112

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

theorem P2M_Projectivization_borel_eq_map_mk__60a95bc3fc91 :
    MeasurableSpace.map
      (mk' K : { v : V // v ≠ 0 } → ℙ K V)
      (borel _) = borel (ℙ K V) := by sorry

alias «Projectivization».«borel_eq_map_mk'» := P2M_Projectivization_borel_eq_map_mk__60a95bc3fc91
