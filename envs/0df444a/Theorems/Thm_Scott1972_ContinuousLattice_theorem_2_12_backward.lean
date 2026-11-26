-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_theorem_2_12_backward
-- name    : Scott1972.ContinuousLattice.theorem_2_12_backward
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:35:54.016795+00:00
-- url     : https://prove2.me/theorems/0c8bd8ad-f2ab-4c33-846e-06f4c9381ce0
-- title:
--   Continuous Lattice: theorem 2 12 backward
-- statement:
--   **Scott 1972, Theorem 2.12 (backward direction).** Every injective `T₀`-space is homeomorphic
--   to a continuous lattice equipped with its Scott topology.
--
--   The injective space `D` is a retract of a power `𝕆^I = (I → Prop)` of the Sierpiński space
--   (Corollary 1.6). Writing `s : D → 𝕆^I` for the embedding and `r : 𝕆^I → D` for the retraction,
--   `e := s ∘ r` is a Scott-continuous idempotent on `𝕆^I` (its topology is its Scott topology by
--   `scottTopology_sierpinskiPower`). The fixed-point set `IdemFix e` is therefore a continuous lattice
--   (`idemFix_isContinuousLattice`, via Proposition 2.10), and `d ↦ s d` is a homeomorphism `D ≃ₜ
--   IdemFix e` with inverse the retraction.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Theorem212.lean#L183-L222
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Theorem212.lean#L183-L222

import Definitions.Def_Scott1972_ContinuousLattice_Constructions
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaces
import Definitions.Def_Scott1972_ContinuousLattice_Theorem212
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
universe u

theorem Scott1972.ContinuousLattice.theorem_2_12_backward {D : Type u} [TopologicalSpace D] [T0Space D]
    (hD : IsInjectiveSpace.{u, u} D) :
    ∃ (E : Type u) (inst : CompleteLattice E),
      @IsContinuousLattice E inst ∧
        Nonempty (@Homeomorph D E _ (@scottTopologicalSpace E inst)) := by sorry
