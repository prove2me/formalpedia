-- Prove2me | Theorems.Thm_TauCeti_exists_differentiableOn_eq_LSeries_ofBadPrimes_sub
-- name    : TauCeti.exists_differentiableOn_eq_LSeries_ofBadPrimes_sub
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:13:21.432486+00:00
-- url     : https://prove2.me/theorems/88514316-77b4-4ce1-9485-57e2e4869cf7
-- title:
--   Continuation after deleting finitely many Dedekind zeta Euler factors
-- statement:
--   Let $K$ be a number field of degree $n$, let $S$ be a finite set of nonzero primes of $\mathcal O_K$, and put
--
--   $$
--   L_S(s)=\zeta_K(s)\prod_{\mathfrak p\in S}(1-(N\mathfrak p)^{-s}),\qquad
--   \rho_S=\rho_K\prod_{\mathfrak p\in S}(1-(N\mathfrak p)^{-1}),
--   $$
--
--   where $\rho_K$ is the residue of $\zeta_K$ at one. There exists $G:\mathbb C\to\mathbb C$, holomorphic on $\operatorname{Re}s>1-1/n$, such that
--
--   $$
--   G(s)=L_S(s)-\frac{\rho_S}{s-1}\qquad(\operatorname{Re}s>1).
--   $$
--
--   This gives the same boundary continuation after imposing finitely many coprimality restrictions on ideals.
--
--   Source: the [Tau Ceti contributors](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/DedekindZeta.lean#L164-L189) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`).
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/DedekindZeta.lean#L164-L189

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Basic
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_NormCoeff
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Weight
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_Ideal
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Algebra.Order.Ring.Units
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Algebra.Ring.Subgroup
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Int.WithZero
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Linearity
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.NumberField.FractionalIdeal
import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Northcott
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.MetricSpace.Pseudo.Real
import Mathlib.Topology.UniformSpace.Real

section
set_option autoImplicit true
namespace TauCeti.GlobalNumberFields
end TauCeti.GlobalNumberFields
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The Dedekind zeta function across the line `Re s = 1`

Let `K` be a number field of degree `d = [K : ℚ]`. The number of nonzero integral ideals of `𝓞 K`
of absolute norm at most `x` is `ρ x + O(x ^ (1 - 1 / d))`, where `ρ = dedekindZeta_residue K`:
summing the ray class ideal counts over the classes of the trivial modulus recovers the total
count, and every class has the same main term.

By partial summation this power saving continues the Dedekind zeta function across the line
`Re s = 1`, with a single simple pole there. Comparing the Dirichlet coefficients of `ζ_K` with
`ρ` times those of the Riemann zeta function, the difference has partial sums `O(n ^ (1 - 1 / d))`,
so its `L`-series continues holomorphically to `Re s > 1 - 1 / d`; and `ζ(s) - 1 / (s - 1)` is
entire (Mathlib's `riemannZeta₀`). Hence `ζ_K(s) - ρ / (s - 1)` agrees on `Re s > 1` with a
function holomorphic on `Re s > 1 - 1 / d`.

Deleting finitely many Euler factors multiplies `ζ_K` by the entire function
`∏ 𝔭 ∈ S, (1 - N(𝔭) ^ (-s))`, so the Dedekind zeta function with the Euler factors at a finite set
`S` of primes deleted has the same kind of continuation, with residue
`ρ * ∏ 𝔭 ∈ S, (1 - N(𝔭) ^ (-1))` at its simple pole `s = 1`. This is the `L`-series of the trivial
member of a family of ideal weights with bad primes `S`, such as the trivial Galois character of a
Galois extension, whose bad primes are the ramified ones.

## Main results

* `TauCeti.setOf_one_le_re_subset_setOf_one_sub_one_div_finrank_lt_re`: the closed half-plane
  `Re s ≥ 1` lies in the half-plane of continuation.
* `TauCeti.isBigO_card_idealsLE_sub`: the number of nonzero integral ideals of norm at most `x` is
  `ρ x + O(x ^ (1 - 1 / [K : ℚ]))`.
* `TauCeti.exists_differentiableOn_eq_dedekindZeta_sub`: `ζ_K(s) - ρ / (s - 1)` extends
  holomorphically from `Re s > 1` to `Re s > 1 - 1 / [K : ℚ]`.
* `TauCeti.exists_differentiableOn_eq_LSeries_ofBadPrimes_sub`: the same for the Dedekind zeta
  function with the Euler factors at a finite set of primes deleted, with the correspondingly
  corrected residue.

## References

* S. Lang, *Algebraic Number Theory*, Chapter VI and Chapter VIII, §3.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter II.1.
-/

 section

open _root_.Asymptotics _root_.Filter _root_.IsDedekindDomain _root_.NumberField _root_.TauCeti.GlobalNumberFields
open scoped _root_.nonZeroDivisors

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti



variable (K : Type*) [Field K] [NumberField K]

-- The nonzero integral ideals of norm at most `x` are those prime to the trivial modulus.




-- The Dirichlet coefficients of `ζ_K` minus `ρ` times those of the Riemann zeta function have
-- partial sums `O(n ^ (1 - 1 / [K : ℚ]))`.

theorem TauCeti.exists_differentiableOn_eq_LSeries_ofBadPrimes_sub (S : _root_.Finset (_root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K))) :
    ∃ G : ℂ → ℂ, _root_.DifferentiableOn ℂ G {s | 1 - 1 / (_root_.Module.finrank ℚ K : ℝ) < s.re} ∧
      ∀ s : ℂ, 1 < s.re → G s = _root_.LSeries (_root_.TauCeti.normCoeff K
          (_root_.TauCeti.MultiplicativeIdealWeight.ofBadPrimes (S : _root_.Set (_root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
            S.finite_toSet).toIdealArithmeticFunction) s -
        _root_.NumberField.dedekindZeta_residue K * (∏ P ∈ S, (1 - (_root_.Ideal.absNorm P.asIdeal : ℂ) ^ (-1 : ℂ))) /
          (s - 1) := by sorry
