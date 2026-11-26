-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_IsContinuousLatticeRetraction_retr_ambientSSup_eq_sSup
-- name    : Scott1972.ContinuousLattice.IsContinuousLatticeRetraction.retr_ambientSSup_eq_sSup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:39:30.605932+00:00
-- url     : https://prove2.me/theorems/0f050454-be84-4a21-91aa-661695ac32c1
-- title:
--   Is Continuous Lattice Retraction: retr ambient SSup eq s Sup
-- statement:
--   **Scott 1972, Prop 2.10 / March 1972 correction (p. 135).** For directed `S ⊆ D`,
--   `j(⊔S′) = ⊔S`: the retraction sends the ambient join back to the subspace join.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L869-L882
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L869-L882

import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Order
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.FixedPoints
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaces
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set Topology TopologicalSpace
universe u v
variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']
open Scott1972.ContinuousLattice.IsContinuousLatticeRetraction

theorem Scott1972.ContinuousLattice.IsContinuousLatticeRetraction.retr_ambientSSup_eq_sSup (R : IsContinuousLatticeRetraction D D') (S : Set D)
    (hS : S.Nonempty) (hdir : DirectedOn (· ≤ ·) S) :
    R.retr (ambientSSup R S) = sSup S := by sorry
