-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_theorem_2_12
-- name    : Scott1972.ContinuousLattice.theorem_2_12
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:41:37.809719+00:00
-- url     : https://prove2.me/theorems/7f1e8eb6-5a72-5904-a2c8-41709e13d135
-- title:
--   Continuous Lattice: theorem 2 12
-- statement:
--   **Scott 1972, Theorem 2.12.** A `T₀`-space is injective iff it is (homeomorphic to) a
--   continuous lattice under its Scott topology. The forward direction is Proposition 2.11; the
--   backward direction is `theorem_2_12_backward`.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Theorem212.lean#L227-L236
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Theorem212.lean#L227-L236

import Definitions.Def_Scott1972_ContinuousLattice_Constructions
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaces
import Definitions.Def_Scott1972_ContinuousLattice_Theorem212
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
universe u

theorem Scott1972.ContinuousLattice.theorem_2_12 {D : Type u} [TopologicalSpace D] [T0Space D] :
    IsInjectiveSpace.{u, u} D ↔
      ∃ (E : Type u) (inst : CompleteLattice E),
        @IsContinuousLattice E inst ∧
          Nonempty (@Homeomorph D E _ (@scottTopologicalSpace E inst)) := by sorry
