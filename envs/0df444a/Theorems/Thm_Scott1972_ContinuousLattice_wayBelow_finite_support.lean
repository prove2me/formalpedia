-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_wayBelow_finite_support
-- name    : Scott1972.ContinuousLattice.wayBelow_finite_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:30:42.655272+00:00
-- url     : https://prove2.me/theorems/64ef58c8-f652-566d-a2b6-6876cef03fd5
-- title:
--   Continuous Lattice: way Below finite support
-- statement:
--   A way-below element of a product has finite support: if `a ≪ z` in `∏ᵢ Eᵢ` then `aⱼ = ⊥` for
--   all but finitely many `j`. The finite truncations `Z F = (fun j => if j ∈ F then z j else ⊥)` form a
--   directed family with supremum `z`; since `a ≪ z = ⊔_F Z F`, already `a ≤ Z F` for some finite `F`,
--   forcing `aⱼ = ⊥` off `F`.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Constructions.lean#L159-L195
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Constructions.lean#L159-L195

import Definitions.Def_Scott1972_ContinuousLattice_MilnerCorrection
import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Definitions.Def_Scott1972_ContinuousLattice_Injective
import Mathlib.Order.Preorder.Finite
import Definitions.Def_Scott1972_ContinuousLattice_Constructions
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
variable {D : Type*} [CompleteLattice D]

theorem Scott1972.ContinuousLattice.wayBelow_finite_support {ι : Type*} {E : ι → Type*} [∀ i, CompleteLattice (E i)]
    {a z : ∀ i, E i} (h : a ≪ z) : ∃ F : Finset ι, ∀ j ∉ F, a j = ⊥ := by sorry
