-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_continuous_eq_sSup_openInfs
-- name    : Scott1972.ContinuousLattice.continuous_eq_sSup_openInfs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:30:28.921914+00:00
-- url     : https://prove2.me/theorems/709c43d5-4136-57b9-bb08-751b479655b8
-- title:
--   Continuous Lattice: continuous eq s Sup open Infs
-- statement:
--   For a continuous `f' : Y → E` into a continuous lattice `E` (with its Scott topology), the
--   value `f' y` is reconstructed as the supremum over open neighbourhoods `U ∋ y` of the meets
--   `⊓ f''(U)`. This is the order-theoretic content behind the maximality clause of Proposition 3.8:
--   the `≤` direction interpolates from below using `f' y = ⊔ {a | a ≪ f' y}` and the openness of each
--   `f'⁻¹(↟a)`; the `≥` direction is immediate since `f' y ∈ f''(U)` whenever `y ∈ U`.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Constructions.lean#L335-L351
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Constructions.lean#L335-L351

import Definitions.Def_Scott1972_ContinuousLattice_MilnerCorrection
import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Definitions.Def_Scott1972_ContinuousLattice_Injective
import Mathlib.Order.Preorder.Finite
import Definitions.Def_Scott1972_ContinuousLattice_Constructions
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
variable {D : Type*} [CompleteLattice D]
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {E : Type*} [CompleteLattice E]

theorem Scott1972.ContinuousLattice.continuous_eq_sSup_openInfs (hE : IsContinuousLattice E) {f' : Y → E}
    (hf' : @Continuous Y E _ scottTopologicalSpace f') (y : Y) :
    f' y = sSup {d | ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧ d = sInf (f' '' U)} := by sorry
