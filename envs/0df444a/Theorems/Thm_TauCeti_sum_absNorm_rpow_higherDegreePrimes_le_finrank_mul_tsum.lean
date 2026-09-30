-- Prove2me | Theorems.Thm_TauCeti_sum_absNorm_rpow_higherDegreePrimes_le_finrank_mul_tsum
-- name    : TauCeti.sum_absNorm_rpow_higherDegreePrimes_le_finrank_mul_tsum
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:06:42.938413+00:00
-- url     : https://prove2.me/theorems/1bb7966d-0300-4c55-bcf3-09d4afd23530
-- title:
--   Comparing higher-degree prime sums with a p-series
-- statement:
--   Let $K$ be a number field with ring of integers $\mathcal O_K$, and write $N(I)=|\mathcal O_K/I|$ for the norm of a nonzero integral ideal. Let $F$ be a finite set of nonzero prime ideals, each of residue degree greater than one over its underlying rational prime. For every real $s>1/2$,
--
--   $$
--   \sum_{P\in F}N(P)^{-s}\le[K:\mathbb Q]\sum_{m=1}^{\infty}m^{-2s}.
--   $$
--
--   The comparison controls higher-residue-degree prime sums in a half-plane extending to the left of one.
--
--   Source and proof credit: the Tau Ceti contributors, [original declaration and proof](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/ArithmeticDirichletSeries/ResidueDegree.lean#L187-L213), Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`; adapted to Lean 4.33.1.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/ArithmeticDirichletSeries/ResidueDegree.lean#L187-L213

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_NumberField_ResidueDegree
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.DirichletDensity
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Northcott
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.UniformSpace.Real

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The primes of residue degree above one are negligible

A height-one prime `𝔭` of `𝓞 K` lies over a unique rational prime `p`, and its absolute norm is
`p ^ f` for `f` the residue degree `Ideal.inertiaDeg 𝔭.asIdeal ℤ`.  This file bounds the
contribution of the primes with `f ≥ 2`, the set `TauCeti.higherDegreePrimes K`: they number
`O(√x)` up to norm `x`, hence also `o(x / log x)`, and their Dirichlet series `∑ N(𝔭) ^ (-s)`
converges for every `s > 1/2`, with a bound that is uniform on `s ≥ 1`.

Two elementary inputs carry the whole argument.

* A prime with `f ≥ 2` has `N(𝔭) = p ^ f ≥ p ^ 2`, so it is *not* determined by a rational prime
  of size `N(𝔭)` but by one of size at most `√(N(𝔭))`.
* At most `[K : ℚ]` height-one primes lie over one rational prime, by the fundamental identity
  `∑ e f = [K : ℚ]`; this is the already available
  `TauCeti.card_filter_rationalPrimeBelow_le_finrank`, itself resting on
  `TauCeti.NumberField.card_primesOverFinset_le_finrank`.

Together these compare any finite sum over the degree-above-one primes with `[K : ℚ]` times a sum
over the rational primes with the exponent doubled, which is
`TauCeti.sum_absNorm_rpow_higherDegreePrimes_le_finrank_mul_tsum` below.  Counting gives the
`O(√x)` bound, and summing `m ^ (-2s)` gives convergence for every `s > 1/2` together with a
bound on the partial Dirichlet series that is *uniform* on `s ≥ 1`.

## Main results

* `TauCeti.primeCount_higherDegreePrimes_le`: the explicit count
  `π_K(x; f ≥ 2) ≤ [K : ℚ] · √x`, with `TauCeti.primeCount_higherDegreePrimes_isBigO` and
  `TauCeti.primeCount_higherDegreePrimes_isLittleO` its `O(√x)` and `o(x / log x)` forms.
* `TauCeti.summable_absNorm_rpow_higherDegreePrimes`: `∑ N(𝔭) ^ (-s)` over the degree-above-one
  primes converges for every `s > 1/2`, in particular at `s = 1`.
* `TauCeti.primeTheta_higherDegreePrimes_isLittleO`: those primes carry weight `o(x)` in `ϑ_K`.
* `TauCeti.primeIdealZetaSum_higherDegreePrimes_le`: that sum, in Mathlib's
  `NumberField.Set.primeIdealZetaSum` vocabulary, is at most `2 [K : ℚ]` for every `s ≥ 1`.
* `TauCeti.sum_absNorm_rpow_le_finrank_mul_tsum` and
  `TauCeti.tsum_absNorm_rpow_le_finrank_mul_tsum`: the same fibring over *all* height-one primes,
  in finite and infinite form, for every `s > 1`.
* `TauCeti.tsum_absNorm_rpow_neg_two_le`: at `s = 2` that becomes the explicit
  `∑_𝔭 N(𝔭) ^ (-2) ≤ 2 [K : ℚ]`.

No density-zero statement is proved here.  What this file supplies is the numerator half of
one: `NumberField.Set.HasDirichletDensity (higherDegreePrimes K) 0` asks for
`primeIdealZetaSum (higherDegreePrimes K) s / primeIdealZetaSum univ s → 0` as `s → 1⁺`, and the
bound below controls only the numerator.  Together with the divergence of the denominator it gives
`TauCeti.hasDirichletDensity_higherDegreePrimes` in
`TauCeti.NumberTheory.ArithmeticDirichletSeries.DirichletDensity.Negligible`.  By contrast
`primeCount K (higherDegreePrimes K) =o[atTop] primeCount K univ`
would need a lower bound on the full prime count, which the prime ideal theorem supplies and
which is not available here; the `o(x / log x)` statement below is against the explicit
function `x / log x`, not against `π_K`.

## Implementation notes

The set `TauCeti.higherDegreePrimes` and the map `TauCeti.rationalPrimeBelow` the estimates fibre
over, together with their elementary norm and inertia theory, are algebraic rather than analytic
and live in `TauCeti.NumberTheory.NumberField.ResidueDegree`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
* J.-P. Serre, *A Course in Arithmetic*, Chapter VI, and J. Milne, *Algebraic Number Theory*,
  Chapter VIII, for the same estimate in the Dirichlet-density setting.
-/

 section

open _root_.Asymptotics _root_.Filter _root_.IsDedekindDomain _root_.NumberField
open scoped _root_.NumberField

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

variable {K : Type*} [Field K] [NumberField K]

/-! ### Fibring a sum over the rational primes below the primes -/





/-! ### Counting the primes of residue degree above one -/











/-! ### Convergence of the prime Dirichlet series over the degree-above-one primes -/

theorem TauCeti.sum_absNorm_rpow_higherDegreePrimes_le_finrank_mul_tsum {s : ℝ} (hs : 1 / 2 < s)
    {F : _root_.Finset (_root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K))} (hF : ∀ 𝔭 ∈ F, 𝔭 ∈ _root_.TauCeti.higherDegreePrimes K) :
    ∑ 𝔭 ∈ F, (_root_.Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) ≤
      _root_.Module.finrank ℚ K * ∑' m : ℕ, (m : ℝ) ^ (-(2 * s)) := by sorry
