-- Prove2me | Theorems.Thm_TauCeti_GlobalNumberFields_exists_abs_ncard_rayFundamentalDomain_inter_norm_le_inter_vadd_sub_le
-- name    : TauCeti.GlobalNumberFields.exists_abs_ncard_rayFundamentalDomain_inter_norm_le_inter_vadd_sub_le
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:12:33.296012+00:00
-- url     : https://prove2.me/theorems/0e562839-31f1-4cda-833a-53d01e7f29f7
-- title:
--   A uniform congruence-lattice count in a ray fundamental domain
-- statement:
--   Let $K$ be a number field and $\mathfrak m=(\mathfrak m_0,\mathfrak m_\infty)$ a modulus, with nonzero integral ideal $\mathfrak m_0$ and a finite set $\mathfrak m_\infty$ of real places. Put $n=[K:\mathbb Q]$ and let $V_K$ be the Minkowski space with standard volume. Let $I$ be an invertible fractional ideal and let $\Lambda$ be the embedded lattice of $I\mathfrak m_0$. Write $D_{\mathfrak m}$ for the ray fundamental domain, $N_V$ for the multiplicative archimedean norm, and $D_1=D_{\mathfrak m}\cap\{N_V\le1\}$. There is $A\ge0$ such that for every $\xi\in V_K$ and every $t\ge1$,
--
--   $$
--   \left|\#\bigl(D_{\mathfrak m}\cap\{N_V\le t\}\cap(\xi+\Lambda)\bigr)
--   -\frac{\operatorname{vol}(D_1)}{\operatorname{covol}(\Lambda)}t\right|
--   \le A t^{1-1/n}.
--   $$
--
--   The constant is independent of the coset, providing a uniform error estimate for ray-class ideal counts.
--
--   Source: the [Tau Ceti contributors](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/Global/Counting/RayFundamentalDomain/LatticeCount.lean#L78-L115) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`).
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/Global/Counting/RayFundamentalDomain/LatticeCount.lean#L78-L115

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_Counting_CongruenceLattice
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_Counting_RayFundamentalDomain_Basic
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Modulus
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Algebra.Order.Ring.Units
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.NumberField.FractionalIdeal
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
# Counting congruence-lattice points in the ray fundamental domain

Let `𝔪` be a modulus of a number field `K` and `I` an invertible fractional ideal.  This file
counts the points of a coset of `congruenceLattice 𝔪 I` inside the dilates of the norm-≤-one
section of `rayFundamentalDomain 𝔪`, with a power-saving error and — the point — with an implied
constant that does not depend on the coset.

Nothing here is new geometry.  The lattice-point count with a power-saving error takes a bounded
region whose frontier is Lipschitz parametrizable in codimension one, and the norm-≤-one section
of the ray fundamental domain has been shown to be exactly that; the congruence lattice has been
shown to be a full `ℤ`-lattice in the mixed space.  This file is the instantiation, and it exists
because the three inputs live in three different developments and the fit between them is the
step that a count of ideals in a fixed ray class actually consumes.

The count is stated for an arbitrary translate `ξ` rather than for the lattice itself because a
fixed ray class corresponds to one coset of the congruence lattice, so every class needs its own
instance of the estimate.  What the statement provides is a single `A` valid for *every* translate
at once, which is the form the class-by-class count consumes directly.

## Main results

* `TauCeti.GlobalNumberFields.exists_abs_ncard_smul_rayFundamentalDomain_inter_vadd_sub_le`: the
  points of any coset of `congruenceLattice 𝔪 I` in the dilate `c •` of the norm-≤-one section
  number `vol / covolume * c ^ [K:ℚ]` up to `O(c ^ ([K:ℚ] - 1))`, uniformly in the coset;
* `TauCeti.GlobalNumberFields.exists_abs_ncard_rayFundamentalDomain_inter_norm_le_inter_vadd_sub_le`
  — the same count graded by the norm: the main term is linear in `t` and the error is
  `O(t ^ (1 - 1 / [K:ℚ]))`.

## References

* S. Lang, *Algebraic Number Theory*, Chapter VI, §2.
-/

 section

open Bornology MeasureTheory Module NumberField NumberField.mixedEmbedding
open scoped Pointwise nonZeroDivisors

namespace TauCeti.GlobalNumberFields
end TauCeti.GlobalNumberFields
section TauCeti.GlobalNumberFields
open TauCeti TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]



open scoped Classical

theorem TauCeti.GlobalNumberFields.exists_abs_ncard_rayFundamentalDomain_inter_norm_le_inter_vadd_sub_le (𝔪 : _root_.TauCeti.GlobalNumberFields.Modulus K)
    (I : (_root_.FractionalIdeal (𝓞 K)⁰ K)ˣ) : ∃ A ≥ (0 : ℝ), ∀ (ξ : _root_.NumberField.mixedEmbedding.mixedSpace K) (t : ℝ), 1 ≤ t →
      |(((_root_.TauCeti.GlobalNumberFields.rayFundamentalDomain 𝔪 ∩ {x : _root_.NumberField.mixedEmbedding.mixedSpace K | mixedEmbedding.norm x ≤ t}) ∩
            (ξ +ᵥ (_root_.TauCeti.GlobalNumberFields.congruenceLattice 𝔪 I : _root_.Set (_root_.NumberField.mixedEmbedding.mixedSpace K)))).ncard : ℝ) -
          volume.real (_root_.TauCeti.GlobalNumberFields.rayFundamentalDomain 𝔪 ∩ {x : _root_.NumberField.mixedEmbedding.mixedSpace K | mixedEmbedding.norm x ≤ 1}) /
            _root_.ZLattice.covolume (_root_.TauCeti.GlobalNumberFields.congruenceLattice 𝔪 I) _root_.MeasureTheory.MeasureSpace.volume * t| ≤
        A * t ^ (1 - ((_root_.Module.finrank ℚ K : ℝ))⁻¹) := by sorry
