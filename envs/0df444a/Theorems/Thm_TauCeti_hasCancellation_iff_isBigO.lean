-- Prove2me | Theorems.Thm_TauCeti_hasCancellation_iff_isBigO
-- name    : TauCeti.hasCancellation_iff_isBigO
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:07:01.964207+00:00
-- url     : https://prove2.me/theorems/704a395f-fde7-4d32-a457-990c69ba618c
-- title:
--   Cancellation is an asymptotic bound
-- statement:
--   Let $K$ be a number field with ring of integers $\mathcal O_K$, and write $N(I)=|\mathcal O_K/I|$ for the norm of a nonzero integral ideal. Let $\chi$ be a unitary ideal weight: it is completely multiplicative, vanishes at only finitely many nonzero prime ideals, and has modulus one on every other nonzero prime ideal. Put $d=[K:\mathbb Q]$, $\alpha=1-1/d$, and $A_\chi(x)=\sum_{0\ne I,\,N(I)\le x}\chi(I)$. Then
--
--   $$
--   \bigl(\exists C\in\mathbb R,\ \forall x\ge1,\ |A_\chi(x)|\le Cx^\alpha\bigr)\quad\Longleftrightarrow\quad A_\chi(x)=O(x^\alpha)\quad(x\to\infty).
--   $$
--
--   The cancellation property can be used interchangeably as a uniform bound or an asymptotic estimate.
--
--   Source and proof credit: the Tau Ceti contributors, [original declaration and proof](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/ArithmeticDirichletSeries/Cancellation.lean#L107-L144), Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`; adapted to Lean 4.33.1.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/ArithmeticDirichletSeries/Cancellation.lean#L107-L144

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Basic
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Cancellation
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Counting
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Weight
import Definitions.Def_TauCeti_Order_Northcott_Basic
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Ring.Subgroup
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.LinearAlgebra.Pi
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Northcott
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
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
# Cancellation in ideal partial sums and the continued L-function of a weight

For a unitary ideal weight `χ` of a number field `K` of degree `d = [K : ℚ]`, the partial sums
`∑_{N(I) ≤ x} χ(I)` over the nonzero integral ideals are trivially `O(x)`, by the linear ideal
count. For nontrivial finite-order ray class characters, equidistribution among ray classes gives
the stronger bound `O(x ^ (1 - 1 / d))`. This file names that bound as a hypothesis and extracts
its analytic consequence.

* `TauCeti.HasCancellation χ` is the uniform bound
  `‖∑_{N(I) ≤ x} χ(I)‖ ≤ C * x ^ (1 - 1 / d)` for every real cutoff `x ≥ 1`, with the inclusive
  summatory function `TauCeti.idealSummatory`.
  Equivalently (`TauCeti.hasCancellation_iff_isBigO`), the partial sums are
  `O(x ^ (1 - 1 / d))` as `x → ∞`.
* `TauCeti.continuedLFunctionOfWeight χ` is the partial-summation integral
  `s * ∫_{1}^{∞} (∑_{N(I) ≤ t} χ(I)) t ^ (-(s + 1)) dt`.

It agrees with the norm-regrouped L-series of `χ` on `Re s > 1` for *every* unitary weight
(`TauCeti.continuedLFunctionOfWeight_eq_LSeries`), and under `HasCancellation χ` it is holomorphic
on `Re s > 1 - 1 / d` (`TauCeti.differentiableOn_continuedLFunctionOfWeight`); so it is an analytic
continuation of the L-series of `χ` across the line `Re s = 1`.

Both are stable under deleting finitely many Euler factors, the operation a character family
needs at the bad primes of its modulus. A one-prime recurrence relates the partial sums after
inserting a forbidden prime to two partial sums before the insertion
(`TauCeti.MultiplicativeIdealWeight.idealSummatory_restrict_insert`). Iterating this recurrence
shows that cancellation passes to the restriction (`TauCeti.HasCancellation.restrict`); on
`Re s > 1` the two continued
`L`-functions differ by the entire factor `∏ 𝔭 ∈ S, (1 - χ(𝔭) N(𝔭) ^ (-s))`
(`TauCeti.continuedLFunctionOfWeight_restrict_of_one_lt_re`), and under cancellation that identity
propagates to the whole half-plane `Re s > 1 - 1 / d`
(`TauCeti.continuedLFunctionOfWeight_restrict`).

In number-field degree greater than one, cancellation is also invariant under purely imaginary
norm twists (`TauCeti.hasCancellation_normTwist_iff`). Abel summation supplies this because the
cancellation exponent `1 - 1 / [K : ℚ]` is then positive. The degree-one case is deliberately not
claimed: the defining bound has exponent zero, while the absolute bound for the Abel integral is
logarithmic.

The continued `L`-function itself follows these operations. Conjugating the weight reflects it
in the real axis, `L(conj χ, conj s) = conj (L(χ, s))`, at every `s`
(`TauCeti.continuedLFunctionOfWeight_conj`). An imaginary norm twist by `N(I) ^ (-z)` translates
it by `z`: on `Re s > 1` for every weight
(`TauCeti.continuedLFunctionOfWeight_normTwist_of_one_lt_re`), and on the whole half-plane
`Re s > 1 - 1 / d` when both the weight and its twist have cancellation
(`TauCeti.continuedLFunctionOfWeight_normTwist`).

Cancellation is a hypothesis about the partial sums themselves. It cannot be replaced by
finiteness of the image of `χ` or of a quotient through which it factors: the values of a weight
factoring through a finite quotient of the free group on the prime ideals can be prescribed
arbitrarily prime by prime.

Nor is it automatic, and `TauCeti.not_hasCancellation_of_isNormTwistOnGood` says which weights it
excludes: those agreeing with a norm twist `I ↦ N(I) ^ (u * I)` on the ideals prime to their bad
primes. The `L`-series of such a weight is the Dedekind zeta function with finitely many Euler
factors deleted, read at `s - u * I`, so it has a pole at `s = 1 + u * I`, where cancellation
would instead make `continuedLFunctionOfWeight χ` holomorphic. The trivial weight
(`TauCeti.not_hasCancellation_one`) and its purely imaginary norm twists
(`TauCeti.not_hasCancellation_normTwist_one`) are the cases a character-family argument meets:
it must not assume cancellation for the degenerate members of its family.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapter 1 (partial summation).
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter II.1.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII §6, for the partial-sum bound of finite-order
  ray class character L-series.
-/

 section

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

open _root_.Filter _root_.Asymptotics _root_.IsDedekindDomain _root_.MeasureTheory
open scoped _root_.ComplexConjugate _root_.nonZeroDivisors _root_.NumberField _root_.Topology

variable {K : Type*} [Field K] [NumberField K]

theorem TauCeti.hasCancellation_iff_isBigO {χ : _root_.TauCeti.UnitaryIdealWeight K} :
    _root_.TauCeti.HasCancellation χ ↔
      (fun x : ℝ ↦ _root_.TauCeti.idealSummatory K χ.toIdealArithmeticFunction x) =O[_root_.Filter.atTop]
        fun x : ℝ ↦ x ^ (1 - 1 / (_root_.Module.finrank ℚ K : ℝ)) := by sorry
