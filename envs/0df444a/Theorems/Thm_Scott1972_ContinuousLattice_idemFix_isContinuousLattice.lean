-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_idemFix_isContinuousLattice
-- name    : Scott1972.ContinuousLattice.idemFix_isContinuousLattice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:38:01.134194+00:00
-- url     : https://prove2.me/theorems/579ce8e9-9b67-4a0b-91b1-e8359998667d
-- title:
--   Continuous Lattice: idem Fix is Continuous Lattice
-- statement:
--   **Fixed points of a Scott-continuous idempotent form a continuous lattice.** Combine the
--   retraction `idemFixRetraction` with Proposition 2.10(a).
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Theorem212.lean#L150-L155
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Theorem212.lean#L150-L155

import Definitions.Def_Scott1972_ContinuousLattice_Constructions
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaces
import Definitions.Def_Scott1972_ContinuousLattice_Theorem212
import Theorems.Thm_Scott1972_ContinuousLattice_preservesDirectedSup_monotone

set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
variable {L : Type*} [CompleteLattice L]
variable {e : L → L}

theorem Scott1972.ContinuousLattice.idemFix_isContinuousLattice (hidem : ∀ x, e (e x) = e x) (hsc : PreservesDirectedSup e)
    (hL : IsContinuousLattice L) :
    @IsContinuousLattice (IdemFix e)
      (IdemFix.completeLattice hidem (preservesDirectedSup_monotone hsc)) := by sorry
