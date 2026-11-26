-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_scottExtend_continuous
-- name    : Scott1972.ContinuousLattice.scottExtend_continuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:30:14.783796+00:00
-- url     : https://prove2.me/theorems/d5f2ed89-fd0c-4a51-a590-415ed7b5973c
-- title:
--   Continuous Lattice: scott Extend continuous
-- statement:
--   The extension is Scott-continuous. For a Scott-open `U` and a point `y₀` with `g y₀ ∈ U`, the
--   basis lemma gives `a ≪ g y₀` with `↟a ⊆ U`; since `g y₀` is a directed supremum, `a ≪ ⊓ f''(e⁻¹V)`
--   for some open `V ∋ y₀`, and that value is `≤ g y'` for every `y' ∈ V`, so `V ⊆ g⁻¹U`.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Constructions.lean#L310-L328
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Constructions.lean#L310-L328

import Definitions.Def_Scott1972_ContinuousLattice_MilnerCorrection
import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Definitions.Def_Scott1972_ContinuousLattice_Injective
import Mathlib.Order.Preorder.Finite
import Definitions.Def_Scott1972_ContinuousLattice_Constructions
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
variable {D : Type*} [CompleteLattice D]
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {E : Type*} [CompleteLattice E]

theorem Scott1972.ContinuousLattice.scottExtend_continuous (hE : IsContinuousLattice E) (e : X → Y) (f : X → E) :
    @Continuous Y E _ scottTopologicalSpace (scottExtend e f) := by sorry
