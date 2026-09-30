-- Prove2me | Theorems.Thm_TauCeti_GlobalNumberFields_frontier_posRegion_subset
-- name    : TauCeti.GlobalNumberFields.frontier_posRegion_subset
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:41:07.895776+00:00
-- url     : https://prove2.me/theorems/4f2e7faf-9549-438b-9498-37d6f99a93c1
-- title:
--   The boundary of an archimedean positivity region
-- statement:
--   Let $K$ be a number field and $\mathfrak m=(\mathfrak m_0,\mathfrak m_\infty)$ a modulus, with nonzero integral ideal $\mathfrak m_0$ and a finite set $\mathfrak m_\infty$ of real places. In the Minkowski space $V_K$, let $P_{\mathfrak m}=\{x:x_w>0\text{ for all }w\in\mathfrak m_\infty\}$. Then
--
--   $$
--   \partial P_{\mathfrak m}\subseteq\bigcup_{w\in\mathfrak m_\infty}\{x\in V_K:x_w=0\}.
--   $$
--
--   This confines the new boundary introduced by sign conditions to finitely many coordinate hyperplanes.
--
--   Source: the [Tau Ceti contributors](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/Global/Counting/RayFundamentalDomain/Lipschitz.lean#L80-L98) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`).
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/Global/Counting/RayFundamentalDomain/Lipschitz.lean#L80-L98

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_Counting_RayFundamentalDomain_Basic
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Modulus
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Order.Ring.Units
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Tactic.Group
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.MetricSpace.HausdorffDimension

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# A Lipschitz parametrization of the frontier of the ray fundamental domain

`TauCeti.NumberTheory.GeometryOfNumbers.LatticePointCount` counts lattice points in a dilated
region with a power-saving error term, but only for regions whose frontier is Lipschitz
parametrizable in codimension one. `NormLeOneLipschitz` discharges that hypothesis for Mathlib's
`normLeOne K`, the norm-≤-one section of the fundamental cone. This file lifts it to the section
`rayFundamentalDomain 𝔪 ∩ {x | mixedEmbedding.norm x ≤ 1}` of the ray fundamental domain of an
arbitrary modulus, which is the region whose lattice points count the algebraic integers in a
fixed ray class.

`rayFundamentalDomain_inter_normLeOne_eq` presents that section as `posRegion 𝔪 ∩ A`, where
`A = ⋃ q, rayUnitRepresentative 𝔪 q • normLeOne K` is a *finite* union of unit translates: the
unit action preserves the mixed norm, so it commutes with the norm condition.

The two factors are of opposite character. `A` is bounded, with a complicated boundary;
`posRegion 𝔪` is an unbounded finite intersection of open half spaces, with a boundary made of
hyperplanes. So the naive `frontier (A ∩ B) ⊆ frontier A ∪ frontier B` is useless here: the
frontier of `posRegion 𝔪` is unbounded, and a Lipschitz-parametrizable set is a finite union of
Lipschitz images of a compact cube, hence bounded — so that union is parametrizable in no
dimension whatsoever. Mathlib's sharp form `frontier_inter_subset` keeps each frontier paired
with the closure of the *other* factor, and that pairing is what makes the argument work:

* `frontier A ∩ closure (posRegion 𝔪)` lies in `frontier A`, which lies in the union of the
  frontiers of the finitely many translates; each `frontier (u • normLeOne K)` is a Lipschitz
  image of `frontier (normLeOne K)`, because a unit acts by a homeomorphism;
* `closure A ∩ frontier (posRegion 𝔪)` is a *bounded* subset of finitely many coordinate
  hyperplanes, and a bounded subset of a hyperplane is Lipschitz parametrizable in codimension
  one (`TauCeti.IsLipschitzParametrizable.of_isBounded_of_subset_ker`).

## Main results

* `TauCeti.GlobalNumberFields.isLipschitzParametrizable_frontier_rayFundamentalDomain`: the
  norm-≤-one section of the ray fundamental domain is bounded and measurable, and its frontier is
  Lipschitz parametrizable in dimension `finrank ℝ (mixedSpace K) - 1`, which is `[K:ℚ] - 1` by
  `mixedEmbedding.finrank`. These are exactly the three hypotheses the lattice-point count with a
  power-saving error consumes, so they are stated together;
* `TauCeti.GlobalNumberFields.isBounded_rayFundamentalDomain_inter_normLeOne` and
  `TauCeti.GlobalNumberFields.measurableSet_rayFundamentalDomain_inter_normLeOne`: the first two
  conclusions on their own, for callers that need only one of them;
* `TauCeti.GlobalNumberFields.rayFundamentalDomain_inter_normLeOne_eq`: that section is the
  positivity region cut by a finite union of unit translates of `normLeOne K`;
* `TauCeti.GlobalNumberFields.frontier_posRegion_subset`: the frontier of the positivity region
  lies in the coordinate hyperplanes prescribed by the infinite part of the modulus.

## References

* C. Birkbeck, [*AINTLIB*](https://github.com/CBirkbeck/AINTLIB) at commit
  `db14b34cc5e3d79603e67c205dfa86b7b989000c` (Apache-2.0),
  `projects/Chebotarev/CebotarevDensity/ForMathlib/IdealCongruenceCount.lean`, which carries out
  the same argument for a sign orthant cut out of a bounded region of `ι → ℝ`:
  `frontier_posRegion_subset` here is that file's `frontier_signOrthant_subset`, and
  `isLipschitzParametrizable_frontier_rayFundamentalDomain` follows its
  `exists_frontier_cover_inter_orthant`, including the use of `frontier_inter_subset` to pair each
  frontier with the other factor's closure. The bounded hyperplane pieces are handled here by the
  general `TauCeti.IsLipschitzParametrizable.of_isBounded_of_subset_ker` rather than by that
  file's explicit slab chart `exists_lipschitz_cube_cover_hyperplane_slab`.
-/

 section

open Module NumberField NumberField.mixedEmbedding
  NumberField.mixedEmbedding.fundamentalCone
open scoped Pointwise

namespace TauCeti.GlobalNumberFields
end TauCeti.GlobalNumberFields
section TauCeti.GlobalNumberFields
open TauCeti TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

theorem TauCeti.GlobalNumberFields.frontier_posRegion_subset (𝔪 : _root_.TauCeti.GlobalNumberFields.Modulus K) :
    _root_.frontier (_root_.TauCeti.GlobalNumberFields.posRegion 𝔪) ⊆ ⋃ w ∈ 𝔪.infinitePart, {x : _root_.NumberField.mixedEmbedding.mixedSpace K | x.1 w = 0} := by sorry
