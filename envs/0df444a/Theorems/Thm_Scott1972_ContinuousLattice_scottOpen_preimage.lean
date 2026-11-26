-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_scottOpen_preimage
-- name    : Scott1972.ContinuousLattice.scottOpen_preimage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:29:33.181635+00:00
-- url     : https://prove2.me/theorems/4f59c418-ac05-5f72-b0b0-601642605698
-- title:
--   Continuous Lattice: scott Open preimage
-- statement:
--   The Continuous Lattice construction uses the scott Open preimage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/ScottMaps.lean#L37-L50
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/ScottMaps.lean#L37-L50

import Definitions.Def_Scott1972_ContinuousLattice_Specialization
import Mathlib.Order.ScottContinuity
import Mathlib.Topology.Order.ScottTopology
import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set Topology
variable {D D' D'' : Type*} [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

theorem Scott1972.ContinuousLattice.scottOpen_preimage {f : D → D'} (hf : PreservesDirectedSup f) {U : Set D'}
    (hU : ScottOpen U) : ScottOpen (f ⁻¹' U) := by sorry
