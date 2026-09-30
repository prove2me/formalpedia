-- Prove2me | Theorems.Thm_TauCeti_abs_ncard_inter_mul_sub_measureReal_le
-- name    : TauCeti.abs_ncard_inter_mul_sub_measureReal_le
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:46:00.688575+00:00
-- url     : https://prove2.me/theorems/5d131027-a395-420d-8347-89c77b847aff
-- title:
--   Lattice counting error controlled by a thickened frontier
-- statement:
--   Let $E$ be a proper normed additive commutative group with its Borel measurable structure, $L\subseteq E$ a discrete additive subgroup, and $\mu$ a locally finite translation-invariant measure. Let $F\subseteq E$ be bounded, measurable and preconnected, with $0\in F$, such that the translates $\ell+F$ for $\ell\in L$ form a disjoint covering of $E$. For every bounded $X\subseteq E$,
--
--   $$
--   \left|\#(X\cap L)\,\mu(F)-\mu(X)\right|
--   \le\#((\partial X-F)\cap L)\,\mu(F).
--   $$
--
--   No measurability hypothesis on $X$ is imposed; $\mu(X)$ denotes its measure value, which is finite for bounded $X$.
--
--   This expresses counting error in terms of boundary cells without requiring regularity of the counted set.
--
--   Source: the [Tau Ceti contributors](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/GeometryOfNumbers/LatticePointCount.lean#L90-L174) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`).
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/GeometryOfNumbers/LatticePointCount.lean#L90-L174

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Connected.Basic
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
# Counting the lattice points of a dilated body, with a boundary-order error

Let `L` be a `ℤ`-lattice in an `n`-dimensional real normed space `E`, let `μ` be an additive Haar
measure on `E`, and let `D` be a bounded set whose frontier is Lipschitz parametrizable in
dimension `n - 1`.  When `0 < n`, the resulting error is power-saving. Dilating `D` by `c`
multiplies its volume by `c ^ n`, and each point of `L` in `c • D` accounts for one cell of the
lattice, of volume `covolume L μ`.  So

```text
#(c • D ∩ L) = μ D / covolume L μ * c ^ n + O(c ^ (n - 1)) as c → ∞.
```

Mathlib's `ZLattice.covolume.tendsto_card_div_pow'` assumes only that the frontier of the body is
null, which gives the limit but no error term at all.  An error term is what a counting argument
needs when the count is one term of a larger asymptotic, and it is what the stronger frontier
hypothesis buys.

## The argument

Fix a fundamental domain `F` for `L`, and call `w + F` the *cell* at a lattice point `w`.  The
cells tile `E`, so the volume of a set `X` is squeezed between the total volume of the cells
contained in `X` and the total volume of the cells meeting `X`, that is, between `#A * μ F` and
`#B * μ F` where

```text
A = {w ∈ L | w + F ⊆ X},   B = {w ∈ L | (w + F) ∩ X ≠ ∅}.
```

Since `0 ∈ F`, a lattice point lies in its own cell, so `A ⊆ X ∩ L ⊆ B` and the count `#(X ∩ L)`
is squeezed between the same two numbers.  Both quantities therefore differ by at most `#(B \ A)`
cells.  A cell counted by `B` and not by `A` meets `X` and its complement; being convex it is
preconnected, so it meets `frontier X` (`IsPreconnected.inter_frontier_nonempty`).  Hence
`B \ A` embeds in the lattice points of the thickened frontier `frontier X + -F`.  That is
`abs_ncard_inter_mul_sub_measureReal_le`, and it holds for any bounded `X`, with no regularity
hypothesis on the frontier: the boundary term is not yet estimated, only identified.

Taking `X = c • D` and `F` the fundamental domain of a basis of `L`, the thickened frontier is
`c • frontier D + -F`, whose lattice points number `O(c ^ (n - 1))` by the boundary count
`TauCeti.IsLipschitzParametrizable.exists_ncard_smul_add_inter_le`.  This is the only place the
Lipschitz hypothesis is used, and the only source of the error term.

## Main results

* `TauCeti.abs_ncard_inter_mul_sub_measureReal_le`: for any bounded set `X`, the count of lattice
  points of `X` times the volume of a fundamental domain `F` differs from the volume of `X` by at
  most the volume of `F` times the number of lattice points of `frontier X + -F`.
* `TauCeti.exists_abs_ncard_smul_inter_vadd_sub_le`: for `c ≥ 1` and *any* coset `ξ +ᵥ L`,
  `|#(c • D ∩ (ξ +ᵥ L)) - μ D / covolume L μ * c ^ n| ≤ A * c ^ (n - 1)`, with `A` independent of
  `c` **and** of `ξ`.
* `TauCeti.isBigO_ncard_smul_inter_sub`: that bound at `ξ = 0`, as an asymptotic statement.
## References

* S. Lang, *Algebraic Number Theory*, Chapter VI, Section 2.
* The coset-uniform count follows C. Birkbeck and R. Brasca,
  [*AINTLIB*](https://github.com/CBirkbeck/AINTLIB) at commit
  `db14b34cc5e3d79603e67c205dfa86b7b989000c` (Apache-2.0),
  `projects/Chebotarev/CebotarevDensity/ForMathlib/IdealCongruenceCount.lean`, theorem
  `exists_card_coset_inter_smul_sub_volume_mul_rpow_le`: the same statement, and the same
  reduction of the translate into a fundamental domain.
-/

 section

open Asymptotics Bornology Filter MeasureTheory Module Set Submodule
open scoped ENNReal Pointwise Topology

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

section Counting

variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
  [MeasurableSpace E] [BorelSpace E] {L : Submodule ℤ E} [DiscreteTopology L]
  {μ : Measure E} [μ.IsAddRightInvariant] [IsLocallyFiniteMeasure μ] {F X : Set E}

theorem TauCeti.abs_ncard_inter_mul_sub_measureReal_le
    (hF₀ : (0 : E) ∈ F) (hFpc : _root_.IsPreconnected F) (hFb : _root_.Bornology.IsBounded F) (hFm : _root_.MeasurableSet F)
    (hFu : ∀ x : E, ∀ w₁ ∈ (L : _root_.Set E), ∀ w₂ ∈ (L : _root_.Set E), x - w₁ ∈ F → x - w₂ ∈ F → w₁ = w₂)
    (hFe : ∀ x : E, ∃ w ∈ (L : _root_.Set E), x - w ∈ F)
    (hXb : _root_.Bornology.IsBounded X) :
    |((X ∩ (L : _root_.Set E)).ncard : ℝ) * μ.real F - μ.real X| ≤
      (((_root_.frontier X + -F) ∩ (L : _root_.Set E)).ncard : ℝ) * μ.real F := by sorry
