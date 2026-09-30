-- Prove2me | Theorems.Thm_TauCeti_primePsi_le_ncard_mul_log
-- name    : TauCeti.primePsi_le_ncard_mul_log
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:08:10.53167+00:00
-- url     : https://prove2.me/theorems/f063e74c-3ac7-472c-9d1b-bc287e0f6a3f
-- title:
--   For x ≥ 1, a finite set of primes contributes at most #S · log x to ψ
-- statement:
--   Let $K$ be a number field with ring of integers $\mathcal O_K$, and write $N(I)=|\mathcal O_K/I|$ for the norm of a nonzero integral ideal. Let $S$ be a finite set of nonzero prime ideals and put $\psi_S(x)=\sum_{P\in S,\ e\ge1,\ N(P)^e\le x}\log N(P)$. For every $x\ge1$,
--
--   $$
--   \psi_S(x)\le |S|\log x.
--   $$
--
--   Finite exceptional prime sets contribute at most logarithmic growth to a prime-power counting function.
--
--   Source and proof credit: the Tau Ceti contributors, [original declaration and proof](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/ArithmeticDirichletSeries/Prime/Psi.lean#L250-L290), Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`; adapted to Lean 4.33.1.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/ArithmeticDirichletSeries/Prime/Psi.lean#L250-L290

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Counting
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Prime_Psi
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Weight
import Definitions.Def_TauCeti_Order_Northcott_Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
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
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Northcott
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
# Chebyshev's `ψ` for a set of prime ideals, and the removal of the higher prime powers

For a set `S` of height-one primes of the ring of integers of a number field `K`, Chebyshev's
`ψ` weights *every* prime power `𝔭 ^ k` with `𝔭 ∈ S` and `k ≥ 1` by `log N(𝔭)`, while `ϑ` weights
only the primes themselves.  This file defines `ψ`, proves that the difference `ψ - ϑ` is exactly
the higher-prime-power sum estimated in
`TauCeti/NumberTheory/ArithmeticDirichletSeries/HigherPrimePowers.lean`, and spends that estimate
on the transfer of an asymptotic `ψ(x) = δ x + o(x)` to `ϑ(x) = δ x + o(x)`.

Prime powers with `k ≥ 2` are kept visible throughout: `ψ` is *defined* with all of them present,
and their removal is a named hypothesis, `TauCeti.HasNegligibleHigherPrimePowers`, discharged for
the standard logarithmic weight by `TauCeti.standardPrimePowerRemoval`.  A different coefficient
system does not get that hypothesis for free; what it has to supply is the domination bound of
`TauCeti.primePowerSummatory_isLittleO_of_le_higherPrimePowerWeight`.

## Main definitions

* `TauCeti.primePowerWeight` is the standard logarithmic prime-power weight, the value `log N(𝔭)`
  at `𝔭 ^ k` for every `k ≥ 1`.  It is the real form of the ideal von Mangoldt function of Layer 2
  on the prime powers.
* `TauCeti.primePsi` is its inclusive summatory function over the prime powers whose base lies in
  `S`: the number-field analogue of Chebyshev's `ψ`.
* `TauCeti.HasNegligibleHigherPrimePowers K S` says that `ψ - ϑ` is `o(x)`.
* `TauCeti.primeVonMangoldtWeight` is the same weight spread over *all* nonzero ideals, zero away
  from the prime powers with base in `S`, and `TauCeti.primeVonMangoldtCoeff` is its regrouping by
  absolute norm, an `ArithmeticFunction ℝ`.

## Main results

* `TauCeti.primePowerSummatory_indicator_sub_primeTheta` splits the exponent-one part off the
  standard weight restricted to any set of prime powers containing exactly the primes of `S`.
* `TauCeti.primePsi_sub_primeTheta` identifies `ψ - ϑ` with the higher-prime-power sum.
* `TauCeti.primePsi_le_ncard_mul_log`: for `x ≥ 1`, a finite set of primes contributes at most
  `#S · log x` to `ψ`, with `TauCeti.primePsi_isBigO_log_of_finite` and
  `TauCeti.primePsi_isLittleO_of_finite` its asymptotic forms.
* `TauCeti.standardPrimePowerRemoval` proves `HasNegligibleHigherPrimePowers K S` for every `S`,
  from the Layer 5 estimate `ψ(x) - ϑ(x) = O(√x log² x)`.
* `TauCeti.primeTheta_asymptotic_of_primePsi` and
  `TauCeti.primePsi_asymptotic_of_primeTheta` transfer a linear asymptotic across that difference,
  with `TauCeti.primeTheta_isEquivalent_of_primePsi` the equivalence form for a nonzero density.
* `TauCeti.primePsi_eq_sum_range` presents `ψ(x)` as the inclusive partial sum
  `∑_{n ≤ ⌊x⌋₊} a n` of the coefficient system, whose coefficients are nonnegative
  (`TauCeti.primeVonMangoldtCoeff_nonneg`) and supported on the prime powers
  (`TauCeti.primeVonMangoldtCoeff_eq_zero_of_not_isPrimePow`).
* `TauCeti.normCoeff_vonMangoldt` identifies the coefficient system of the full prime carrier with
  the Layer 1 regrouping of the Layer 2 ideal von Mangoldt function.
* `TauCeti.primeVonMangoldtCoeff_rat_natGenerator_pow` evaluates the coefficient system of any set
  of primes of `𝓞 ℚ` at a prime power, and `TauCeti.primeVonMangoldtCoeff_rat_le` bounds it by
  Mathlib's von Mangoldt function `Λ`.

## Roadmap role

This is Layer **10.2** of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`: "For the fixed
standard nonnegative logarithmic prime-power weight, use Layer 5 to prove
`standardPrimePowerRemoval : HasNegligibleHigherPrimePowers K S` and make
`primeTheta_asymptotic_of_primePsi` consume that named estimate."  It also supplies the arithmetic
half of Layer **10.1**, "Define `primePsi` with all prime powers present": the exact nonnegative
von Mangoldt coefficient system and the identity presenting `ψ` as its partial sum, which is the
shape in which a Tauberian theorem delivers its conclusion.  The analytic boundary package and
the resulting prime-number-theorem transfer are in
`TauCeti/NumberTheory/ArithmeticDirichletSeries/Prime/Boundary.lean`.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapter 7.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter I.2.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII.

The rational-prime case of `ψ`, `ϑ` and their difference is Mathlib's
`Mathlib/NumberTheory/Chebyshev.lean`, whose `Chebyshev.theta_le_psi` and
`Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log` are the analogues of
`TauCeti.primeTheta_le_primePsi` and `TauCeti.standardPrimePowerRemoval`; nothing is transported
from there, since the estimate consumed here is proved over prime ideals in Layer 5.
-/

 section

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

open _root_.Filter _root_.NumberField
open scoped _root_.Asymptotics _root_.nonZeroDivisors _root_.NumberField
open _root_.IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K]

/-! ### The standard logarithmic prime-power weight -/















/-! ### Chebyshev's `ψ` -/



variable {S : Set (HeightOneSpectrum (𝓞 K))} {x δ : ℝ}











/-! ### The higher prime powers as the gap between `ψ` and `ϑ` -/







/-! ### Removing the higher prime powers -/

theorem TauCeti.primePsi_le_ncard_mul_log (hS : S.Finite) (hx : 1 ≤ x) :
    _root_.TauCeti.primePsi K S x ≤ S.ncard * _root_.Real.log x := by sorry
