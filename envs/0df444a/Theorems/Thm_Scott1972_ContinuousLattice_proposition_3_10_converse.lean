-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_proposition_3_10_converse
-- name    : Scott1972.ContinuousLattice.proposition_3_10_converse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:40:10.697258+00:00
-- url     : https://prove2.me/theorems/6b11a80b-a6f6-439e-85e0-e0336214b274
-- title:
--   Continuous Lattice: proposition 3 10 converse
-- statement:
--   **Scott 1972, Proposition 3.10 (converse).** If `i : D → D'` (between continuous lattices)
--   satisfies (i) preservation of arbitrary suprema, (ii) injectivity, and (iii) preservation of `≪`,
--   then there is a continuous `j` making `D` a projection of `D'` via `i`, with `j` given by Scott's
--   formula (iv) `j(x') = ⊔ { x | i(x) ⊑ x' }`.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L1290-L1296
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L1290-L1296

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
open Finset
variable {i : D → D'}

theorem Scott1972.ContinuousLattice.proposition_3_10_converse
    (hi : ∀ S : Set D, i (sSup S) = sSup (i '' S)) (hinj : Function.Injective i)
    (hwb : ∀ {x y : D}, x ≪ y → i x ≪ i y) (hD : IsContinuousLattice D) :
    ∃ P : IsContinuousLatticeProjection D D',
      (∀ d, (P.incl : D → D') d = i d)
        ∧ (∀ x', (P.retr : D' → D) x' = sSup {x | i x ≤ x'}) := by sorry
