-- Prove2me | Theorems.Thm_TauCeti_normCoeff_delta
-- name    : TauCeti.normCoeff_delta
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:34:02.638984+00:00
-- url     : https://prove2.me/theorems/3d9ce875-7450-4aa9-bf01-0f93cbc634e1
-- title:
--   Norm coefficients preserve the convolution identity
-- statement:
--   Let $K$ be a number field with ring of integers $\mathcal O_K$, and write $N(I)=|\mathcal O_K/I|$ for the norm of a nonzero integral ideal. Define the ideal delta function by $\delta(I)=1$ for $I=\mathcal O_K$ and $\delta(I)=0$ otherwise. Let $a_\delta(n)=\sum_{N(I)=n}\delta(I)$, where the sum ranges over nonzero ideals. Then
--
--   $$
--   a_\delta(n)=\begin{cases}1,&n=1,\\0,&n\ne1.\end{cases}
--   $$
--
--   Norm regrouping preserves the identity element for Dirichlet convolution.
--
--   Source and proof credit: the Tau Ceti contributors, [original declaration and proof](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/ArithmeticDirichletSeries/Convolution.lean#L398-L415), Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`; adapted to Lean 4.33.1.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/ArithmeticDirichletSeries/Convolution.lean#L398-L415

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Basic
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Convolution
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_NormCoeff
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Ring.Subgroup
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.LinearAlgebra.Pi
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Tactic.Ring

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Ideal convolution of ideal arithmetic functions

The Dirichlet convolution of two arithmetic functions on the nonzero ideals of the ring of integers
of a number field `K` sums over the factorizations `B * C = A` of a nonzero ideal `A`. This file
constructs that index set, defines the convolution, and proves that it makes
`TauCeti.IdealArithmeticFunction K` a commutative monoid with identity
`TauCeti.IdealArithmeticFunction.delta`, bilinear over the pointwise additive structure.
It also transports this operation through `TauCeti.normCoeff` to Mathlib's Dirichlet convolution
on `ArithmeticFunction ℂ`.

## Main definitions

* `TauCeti.IdealArithmeticFunction.delta` is the ideal arithmetic function that is `1` at the unit
  ideal and `0` elsewhere.
* `TauCeti.Ideal.divisorsAntidiagonal A` is the finite set of pairs `(B, C)` of nonzero ideals with
  `B * C = A`; it is the ideal analogue of Mathlib's `Nat.divisorsAntidiagonal`.
* `TauCeti.IdealArithmeticFunction.convolution f g` is the ideal Dirichlet convolution.
* `TauCeti.IdealArithmeticFunction.convolutionPow f n` is the `n`-fold convolution power of `f`.

## Main results

* `TauCeti.IdealArithmeticFunction.convolution_comm`,
  `TauCeti.IdealArithmeticFunction.convolution_assoc`,
  `TauCeti.IdealArithmeticFunction.delta_convolution` and
  `TauCeti.IdealArithmeticFunction.convolution_delta`: the convolution monoid laws.
* `TauCeti.IdealArithmeticFunction.convolution_add` and
  `TauCeti.IdealArithmeticFunction.add_convolution`: bilinearity over pointwise addition.
* `TauCeti.IdealArithmeticFunction.convolution_one_one_ne_mul`: ideal convolution is not the
  pointwise product.
* `TauCeti.normCoeff_delta`, `TauCeti.normCoeff_convolution`, and
  `TauCeti.normCoeff_convolutionPow`: regrouping by absolute norm transports the convolution
  identity, convolution, and convolution powers to Mathlib arithmetic functions.

## Implementation notes

`TauCeti.IdealArithmeticFunction K` is a `Pi` type, so it already carries Mathlib's *pointwise*
`CommRing` structure, in which `f * g` is `fun A => f A * g A` and `1` is the everywhere-one
function. Convolution is therefore deliberately **not** registered as a `Mul` instance and its
identity is the separate function `TauCeti.IdealArithmeticFunction.delta`; this is the roadmap's
convention that pointwise multiplication and ideal convolution stay distinct operations on one
carrier. The monoid laws are stated as ordinary theorems about
`TauCeti.IdealArithmeticFunction.convolution`, and
`TauCeti.IdealArithmeticFunction.convolution_one_one_ne_mul` records that the two products really do
differ. Consequently iterated convolution is the explicit
`TauCeti.IdealArithmeticFunction.convolutionPow` rather than a `Monoid.npow`.

Excluding the zero ideal from the carrier is what makes the index set finite: `⊥ * J = ⊥` for every
`J`, so the zero ideal has infinitely many factorizations while a nonzero ideal has only finitely
many, by Mathlib's `UniqueFactorizationMonoid.fintypeSubtypeDvd` for the unique factorization
monoid `Ideal (𝓞 K)`.

## Roadmap role

This is Layer **2.1** of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`, built on the Layer
**0.1** carrier of `TauCeti/NumberTheory/ArithmeticDirichletSeries/Basic.lean`. Its consumers are
the ideal Möbius function and von Mangoldt transform of Layer 2 and the local factors of Layer 3.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapters II--III.
-/

 section

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

open scoped nonZeroDivisors NumberField

namespace TauCeti.IdealArithmeticFunction
end TauCeti.IdealArithmeticFunction
section IdealArithmeticFunction
open TauCeti TauCeti.IdealArithmeticFunction

variable {K : Type*} [Field K]

/-! ### The convolution identity -/









end IdealArithmeticFunction

variable {K : Type*} [Field K] [NumberField K]

namespace TauCeti.Ideal
end TauCeti.Ideal
section Ideal
open TauCeti TauCeti.Ideal

/-! ### The antidiagonal of a nonzero ideal -/

















end Ideal

namespace TauCeti.IdealArithmeticFunction
end TauCeti.IdealArithmeticFunction
section IdealArithmeticFunction
open TauCeti TauCeti.IdealArithmeticFunction

/-! ### Ideal convolution -/







/-! ### The monoid laws -/









/-! ### Bilinearity over the pointwise additive structure -/





















/-! ### Iterated convolution -/













/-! ### Convolution is not the pointwise product -/





end IdealArithmeticFunction

/-! ## Compatibility with Dirichlet convolution -/

variable (K : Type*) [Field K] [NumberField K]

@[simp]
theorem TauCeti.normCoeff_delta : _root_.TauCeti.normCoeff K _root_.TauCeti.IdealArithmeticFunction.delta = 1 := by sorry
