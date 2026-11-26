-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_proposition_3_14
-- name    : Scott1972.ContinuousLattice.proposition_3_14
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:41:29.073824+00:00
-- url     : https://prove2.me/theorems/eb138025-fbe6-4064-9af0-f6cc3fe7faff
-- title:
--   Continuous Lattice: proposition 3 14
-- statement:
--   **Scott 1972, Proposition 3.14.** For a continuous lattice `D` there is a uniquely determined
--   continuous mapping `fix : [D → D] → D` such that `f (fix f) = fix f` for all `f`, and `fix f ⊑ x`
--   whenever `f x ⊑ x`. Existence and continuity are `Proposition314.fixMap`; the defining equations are
--   `fix_eq`/`fix_le`; uniqueness (any operator with these two properties agrees with `fix`) is
--   `fix_unique`.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L1745-L1755
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L1745-L1755

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

theorem Scott1972.ContinuousLattice.proposition_3_14 (_hD : IsContinuousLattice D) :
    ∃ Fix : ScottMap (ScottMap D D) D,
      (∀ f : ScottMap D D, (f : D → D) (Fix f) = Fix f)
        ∧ (∀ (f : ScottMap D D) (x : D), (f : D → D) x ≤ x → (Fix f : D) ≤ x)
        ∧ (∀ g : ScottMap D D → D,
            (∀ f : ScottMap D D, (f : D → D) (g f) = g f) →
            (∀ (f : ScottMap D D) (x : D), (f : D → D) x ≤ x → g f ≤ x) →
            ∀ f : ScottMap D D, g f = Fix f) := by sorry
