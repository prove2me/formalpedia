-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_directedOn_finite_sSup_mem
-- name    : Scott1972.ContinuousLattice.directedOn_finite_sSup_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:30:32.676255+00:00
-- url     : https://prove2.me/theorems/4ff0e7a5-d407-5dcf-bbcb-911e10da60fd
-- title:
--   Continuous Lattice: directed On finite s Sup mem
-- statement:
--   A non-empty **finite** directed set attains its supremum: `⊔S ∈ S`. A maximal element of
--   `S` (which exists by finiteness) is, by directedness, the greatest element, hence the
--   supremum. This is the order-theoretic heart of "finite ⟹ continuous" (Scott 1972, 2.8).
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Constructions.lean#L36-L45
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Constructions.lean#L36-L45

import Definitions.Def_Scott1972_ContinuousLattice_MilnerCorrection
import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Definitions.Def_Scott1972_ContinuousLattice_Injective
import Mathlib.Order.Preorder.Finite
import Definitions.Def_Scott1972_ContinuousLattice_Constructions
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
variable {D : Type*} [CompleteLattice D]

theorem Scott1972.ContinuousLattice.directedOn_finite_sSup_mem {S : Set D} (hSfin : S.Finite) (hSne : S.Nonempty)
    (hSdir : DirectedOn (· ≤ ·) S) : sSup S ∈ S := by sorry
