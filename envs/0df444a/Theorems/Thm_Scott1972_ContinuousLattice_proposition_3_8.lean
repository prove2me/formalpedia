-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_proposition_3_8
-- name    : Scott1972.ContinuousLattice.proposition_3_8
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:32:22.194952+00:00
-- url     : https://prove2.me/theorems/d3686c98-4ff0-5901-9b52-45663109e27e
-- title:
--   Continuous Lattice: proposition 3 8
-- statement:
--   **Scott 1972, Proposition 3.8.** If `E` is a continuous lattice and `e : X → Y` a subspace
--   embedding, then for each continuous `f : X → E` the explicit formula `scottExtend e f` is the
--   *maximal extension* of `f` to `[Y → E]`: it is Scott-continuous (`scottExtend_continuous`), it
--   restricts to `f` along `e` (`scottExtend_eq_of_continuous`), and it dominates every continuous
--   solution of `f' ∘ e = f` (`scottExtend_maximal`).
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Constructions.lean#L389-L397
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Constructions.lean#L389-L397

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

theorem Scott1972.ContinuousLattice.proposition_3_8 (hE : IsContinuousLattice E) (e : X → Y) (he : IsEmbedding e)
    (f : X → E) (hf : @Continuous X E _ scottTopologicalSpace f) :
    @Continuous Y E _ scottTopologicalSpace (scottExtend e f)
      ∧ (∀ x, scottExtend e f (e x) = f x)
      ∧ (∀ f' : Y → E, @Continuous Y E _ scottTopologicalSpace f' → (∀ x, f' (e x) = f x) →
          ∀ y, f' y ≤ scottExtend e f y) := by sorry
