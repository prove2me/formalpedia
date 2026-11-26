-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_scottExtend_eq_of_continuous
-- name    : Scott1972.ContinuousLattice.scottExtend_eq_of_continuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:30:09.921794+00:00
-- url     : https://prove2.me/theorems/e3a16052-90ca-55e1-8377-5a86b042a700
-- title:
--   Continuous Lattice: scott Extend eq of continuous
-- statement:
--   The extension agrees with `f` on the (embedded) subspace. The `≤` direction is immediate
--   (`f x₀` is one of the values being met); the `≥` direction uses continuity of `E`: for each
--   `a ≪ f x₀` the Scott-open `↟a` pulls back along the continuous `f` and, by the embedding, to an
--   open `V ⊆ Y` on whose `e`-preimage `f ≥ a`, so `a ≤ ⊓ f''(e⁻¹V) ≤ g(e x₀)`.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Constructions.lean#L286-L305
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Constructions.lean#L286-L305

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

theorem Scott1972.ContinuousLattice.scottExtend_eq_of_continuous (hE : IsContinuousLattice E) (e : X → Y)
    (he : IsEmbedding e) (f : X → E) (hf : @Continuous X E _ scottTopologicalSpace f) (x₀ : X) :
    scottExtend e f (e x₀) = f x₀ := by sorry
