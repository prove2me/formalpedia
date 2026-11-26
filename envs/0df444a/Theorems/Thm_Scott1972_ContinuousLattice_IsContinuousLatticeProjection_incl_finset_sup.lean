-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_IsContinuousLatticeProjection_incl_finset_sup
-- name    : Scott1972.ContinuousLattice.IsContinuousLatticeProjection.incl_finset_sup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:37:26.248049+00:00
-- url     : https://prove2.me/theorems/a9803e38-dfbf-4da3-bfc5-ac20930a4651
-- title:
--   Is Continuous Lattice Projection: incl finset sup
-- statement:
--   The Is Continuous Lattice Projection construction uses the incl finset sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L1070-L1078
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L1070-L1078

import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Order
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.FixedPoints
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaces
import Theorems.Thm_Scott1972_ContinuousLattice_WayBelow_sup

set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set Topology TopologicalSpace
universe u v
variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']
open Finset
open Scott1972.ContinuousLattice.IsContinuousLatticeProjection

theorem Scott1972.ContinuousLattice.IsContinuousLatticeProjection.incl_finset_sup (P : IsContinuousLatticeProjection D D') (T : Finset D) :
    P.incl (T.sup (fun x => x)) = T.sup (fun x => P.incl x) := by sorry
