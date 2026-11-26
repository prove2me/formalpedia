-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_scottOpen_of_coarserThanScott
-- name    : Scott1972.ContinuousLattice.scottOpen_of_coarserThanScott
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:31:59.170968+00:00
-- url     : https://prove2.me/theorems/90f322d0-d3e9-5f04-8e0a-11030115b793
-- title:
--   Continuous Lattice: scott Open of coarser Than Scott
-- statement:
--   The Continuous Lattice construction uses the scott Open of coarser Than Scott property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/MilnerCorrection.lean#L59-L61
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/MilnerCorrection.lean#L59-L61

import Definitions.Def_Scott1972_ContinuousLattice_Specialization
import Definitions.Def_Scott1972_ContinuousLattice_MilnerCorrection
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set Topology
variable {D D' : Type*} [CompleteLattice D] [CompleteLattice D']

theorem Scott1972.ContinuousLattice.scottOpen_of_coarserThanScott {τ : TopologicalSpace D} (hτ : CoarserThanScottTopology τ)
    {U : Set D} (hU : @IsOpen D τ U) : ScottOpen U := by sorry
