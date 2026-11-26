-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_theorem_2_12_injective_half
-- name    : Scott1972.ContinuousLattice.theorem_2_12_injective_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:33:17.376673+00:00
-- url     : https://prove2.me/theorems/bbd41854-5380-4f2b-a510-eef3e1f4008d
-- title:
--   Continuous Lattice: theorem 2 12 injective half
-- statement:
--   **Scott 1972, Theorem 2.12 (injectivity half, unconditional).** `Prop` is injective
--   (Sierpiński); the continuous-lattice half is now `isContinuousLattice_prop`.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Constructions.lean#L506-L507
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Constructions.lean#L506-L507

import Definitions.Def_Scott1972_ContinuousLattice_MilnerCorrection
import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Definitions.Def_Scott1972_ContinuousLattice_Injective
import Mathlib.Order.Preorder.Finite
import Definitions.Def_Scott1972_ContinuousLattice_Constructions
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
variable {D : Type*} [CompleteLattice D]

theorem Scott1972.ContinuousLattice.theorem_2_12_injective_half : IsInjectiveSpace Prop := by sorry
