-- Prove2me | Theorems.Thm_TauCeti_IsLipschitzParametrizable_exists_ncard_smul_add_inter_le
-- name    : TauCeti.IsLipschitzParametrizable.exists_ncard_smul_add_inter_le
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:46:09.415408+00:00
-- url     : https://prove2.me/theorems/edef1668-2484-4861-88b7-e75da4e2e0cc
-- title:
--   Counting discrete subgroup points near a parametrized boundary
-- statement:
--   Let $E$ be a proper real normed vector space, let $L\subseteq E$ be a discrete additive subgroup, and let $B\subseteq E$ be bounded. Suppose $S\subseteq E$ is covered by finitely many images of the $d$-dimensional unit cube under Lipschitz maps, where $d\in\mathbb N$. There is $A\ge0$ such that
--
--   $$
--   \#((cS+B)\cap L)\le A c^d\qquad(c\ge1).
--   $$
--
--   Here $cS$ is scalar dilation and $cS+B$ is the Minkowski sum.
--
--   This controls the number of lattice cells near a dilated boundary and provides the error term in lattice-point estimates.
--
--   Source: the [Tau Ceti contributors](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/GeometryOfNumbers/BoundaryCount.lean#L73-L159) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`).
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/GeometryOfNumbers/BoundaryCount.lean#L73-L159

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_Topology_MetricSpace_LipschitzParametrizable
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.MetricSpace.Pseudo.Real

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Counting points of a discrete subgroup near a dilated Lipschitz-parametrizable set

Let `L` be a discrete additive subgroup of a proper normed real vector space `E`, and let `S ⊆ E` be
Lipschitz parametrizable in dimension `d`, that is, covered by finitely many Lipschitz images of
the unit `d`-cube.  Dilating `S` by a factor `c ≥ 1` and thickening it by a fixed bounded set `B`
produces a region that carries `O(c ^ d)` points of `L`.

This is the quantitative half of Lipschitz parametrizability.  When `d` is strictly smaller than
the ambient dimension, as in the codimension-one boundary application, it is a genuinely smaller
order than the `c ^ (dim E)` points carried by a dilated body and hence gives a power-saving error
term in a lattice-point count.  The thickening by `B` is what the application needs: the lattice
cells `x + F` that meet a dilated region `c • S` are exactly the `x ∈ L` lying in
`c • S + (-F)`, so a count of cells meeting the boundary of a dilated body is a count of the
points of `L` in such a region.

The proof subdivides the unit cube into `m ^ d` subcubes of side `1 / m`, with `m` of size
`c`, so that each chart maps a subcube into a set of diameter at most one after dilating by `c`.
Translation invariance bounds the number of points of `L` in any set of bounded diameter by a
constant, so the total count is at most a constant times the number `m ^ d` of subcubes.

## Main results

* `TauCeti.IsLipschitzParametrizable.finite_smul_add_inter`: a bounded thickening of a dilated
  Lipschitz-parametrizable set meets a discrete subgroup in a finite set.
* `TauCeti.IsLipschitzParametrizable.exists_ncard_smul_add_inter_le`: the explicit bound
  `#((c • S + B) ∩ L) ≤ A * c ^ d` for `c ≥ 1`, with `A` independent of `c`.
* `TauCeti.IsLipschitzParametrizable.isBigO_ncard_smul_add_inter`: the same bound as an
  asymptotic statement, `#((c • S + B) ∩ L) = O(c ^ d)` as `c → ∞`.

## References

* S. Lang, *Algebraic Number Theory*, Chapter VI, Section 2.
-/

 section

open Asymptotics Bornology Filter Metric Set
open scoped Pointwise Topology

namespace TauCeti.IsLipschitzParametrizable
end TauCeti.IsLipschitzParametrizable
section TauCeti.IsLipschitzParametrizable
open TauCeti TauCeti.IsLipschitzParametrizable

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

theorem TauCeti.IsLipschitzParametrizable.exists_ncard_smul_add_inter_le {d : ℕ} {S : _root_.Set E}
    (hS : _root_.TauCeti.IsLipschitzParametrizable d S) (L : _root_.AddSubgroup E) [_root_.DiscreteTopology L]
    {B : _root_.Set E} (hB : _root_.Bornology.IsBounded B) :
    ∃ A ≥ (0 : ℝ), ∀ c : ℝ, 1 ≤ c →
      (((c • S + B) ∩ (L : _root_.Set E)).ncard : ℝ) ≤ A * c ^ d := by sorry
