-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_sierpinski_isInjective_and_isContinuousLattice
-- name    : Scott1972.ContinuousLattice.sierpinski_isInjective_and_isContinuousLattice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:33:49.277978+00:00
-- url     : https://prove2.me/theorems/9718ae60-f70a-551b-b2f4-bd07b7d4a842
-- title:
--   Continuous Lattice: sierpinski is Injective and is Continuous Lattice
-- statement:
--   The Sierpiński space `𝕆 = Prop` realizes the smallest case of Theorem 2.12: it is both
--   injective (1.2) and a continuous lattice (2.8).
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Constructions.lean#L511-L513
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Constructions.lean#L511-L513

import Definitions.Def_Scott1972_ContinuousLattice_MilnerCorrection
import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Definitions.Def_Scott1972_ContinuousLattice_Injective
import Mathlib.Order.Preorder.Finite
import Definitions.Def_Scott1972_ContinuousLattice_Constructions
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
variable {D : Type*} [CompleteLattice D]

theorem Scott1972.ContinuousLattice.sierpinski_isInjective_and_isContinuousLattice :
    IsInjectiveSpace Prop ∧ IsContinuousLattice Prop := by sorry
