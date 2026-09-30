-- Prove2me | Theorems.Thm_TauCeti_MultiplicativeIdealWeight_logDeriv_LSeries_eq_neg_tsum_vonMangoldtTransform
-- name    : TauCeti.MultiplicativeIdealWeight.logDeriv_LSeries_eq_neg_tsum_vonMangoldtTransform
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:11:45.613655+00:00
-- url     : https://prove2.me/theorems/b4929e6e-dad5-4333-8be7-3c8f54f55bc3
-- title:
--   The coefficient identity for the logarithmic derivative
-- statement:
--   Let $K$ be a number field with ring of integers $\mathcal O_K$, and write $N(I)=|\mathcal O_K/I|$ for the norm of a nonzero integral ideal. Let $\chi$ be a completely multiplicative complex weight on integral ideals, preserving zero and one, with only finitely many zero values at nonzero prime ideals. Write $L_\chi(s)=\sum_{n\ge1}a_\chi(n)n^{-s}$, with $a_\chi(n)=\sum_{N(I)=n}\chi(I)$. Define $\Lambda_K(P^e)=\log N(P)$ for primes $P$ and $e\ge1$, and zero off the prime powers. If $\operatorname{Re}s$ is strictly greater than the abscissa of absolute convergence of the ideal-indexed series of $\chi$, then
--
--   $$
--   \frac{L_\chi^{\prime}(s)}{L_\chi(s)}=-\sum_{I\ne0}\chi(I)\Lambda_K(I)N(I)^{-s}.
--   $$
--
--   The coefficients of the negative logarithmic derivative are the von Mangoldt transform of the ideal weight.
--
--   Source and proof credit: the Tau Ceti contributors, [original declaration and proof](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/ArithmeticDirichletSeries/EulerProduct/Logarithm/VonMangoldtCoeff.lean#L135-L172), Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`; adapted to Lean 4.33.1.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/ArithmeticDirichletSeries/EulerProduct/Logarithm/VonMangoldtCoeff.lean#L135-L172

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Basic
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_EulerProduct_Data
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_NormCoeff
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Regroup
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_VonMangoldt
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Weight
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Ring.Subgroup
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.LinearAlgebra.Pi
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.NumberTheory.EulerProduct.ExpLog
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
import Mathlib.RingTheory.PowerSeries.Log
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
# The logarithmic derivative as a von Mangoldt Dirichlet series

Strictly to the right of the abscissa of absolute convergence,

`logDeriv L(s) = -∑' A, χ(A) Λ(A) / N(A) ^ s`,

the sum running over the nonzero integral ideals of `𝓞 K`, with `Λ` the ideal von Mangoldt
function. This is the coefficient identity: it names the exact Dirichlet coefficients of the
logarithmic derivative, which is what a Tauberian argument consumes.

The prime-power expansion of `logDeriv_LSeries_eq_tsum_prime_pow` is the same sum written over
`(𝔭, k)`. The two agree termwise, because the von Mangoldt transform of a completely multiplicative
weight at `𝔭 ^ (k+1)` is `χ(𝔭) ^ (k+1) log N(𝔭)` and `N(𝔭 ^ (k+1)) = N(𝔭) ^ (k+1)`; the transform
vanishes off the prime powers, so nothing else contributes.

For general Euler-product data `D`, whose values at higher prime powers are independent, the
coefficient at `𝔭 ^ e` is `log N(𝔭)` times the degree-`e` coefficient of the local series
`X F_𝔭'/F_𝔭`. This defines the von Mangoldt function `Λ_D` of `D`, which is the von Mangoldt
transform of the weight in the completely multiplicative case. Where the local power series are
zero-free on the disks of absolute convergence, `-logDeriv L(s) = ∑' A, Λ_D(A) / N(A) ^ s`, with
absolute convergence.

## Main definitions

* `TauCeti.EulerProductData.vonMangoldt`: the von Mangoldt function `Λ_D` of Euler-product data.

## Main results

* `TauCeti.IdealArithmeticFunction.summable_idealTerm_vonMangoldtTransform`: the von Mangoldt
  weighted ideal terms are summable on the half-plane, for any ideal arithmetic function.
* `TauCeti.MultiplicativeIdealWeight.logDeriv_LSeries_eq_neg_tsum_vonMangoldtTransform`: the
  coefficient identity for a completely multiplicative weight.
* `TauCeti.EulerProductData.vonMangoldt_ofMultiplicativeIdealWeight`: `Λ_D` of a completely
  multiplicative weight is its von Mangoldt transform.
* `TauCeti.EulerProductData.hasSum_idealTerm_vonMangoldt_of_zeroFree` and
  `TauCeti.EulerProductData.LSeriesHasSum_normCoeff_vonMangoldt_of_zeroFree`: the coefficient
  identity for general Euler-product data, ideal-indexed and regrouped by norm.

## Implementation notes

Summability is comparison against `TauCeti.summable_log_absNorm_mul_norm_idealTerm_of_re_lt_re`,
whose weight `log N(I)` dominates `‖Λ(I)‖` by `norm_vonMangoldt_le_log`. Passing from the
`(𝔭, k)`-indexed sum to the ideal-indexed one is
`TauCeti.tsum_eq_tsum_idealPrimePower_of_support_subset`.

For general `D`, `PowerSeries.tsum_norm_coeff_logDeriv_mul_pow_succ_le` supplies the local
majorant that gives absolute convergence of the von Mangoldt series. The general coefficient
identity applies to data with an absolute-convergence point `σ` and zero-free local series on the
corresponding disks.

## References

* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter I.2.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, §5.1, for the von Mangoldt function of
  a general Euler product.
-/

 section

open scoped nonZeroDivisors NumberField
open IsDedekindDomain NumberField

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

namespace TauCeti.IdealArithmeticFunction
end TauCeti.IdealArithmeticFunction
section IdealArithmeticFunction
open TauCeti TauCeti.IdealArithmeticFunction

variable {K : Type*} [Field K] [NumberField K]



end IdealArithmeticFunction

namespace TauCeti.MultiplicativeIdealWeight
end TauCeti.MultiplicativeIdealWeight
section MultiplicativeIdealWeight
open TauCeti TauCeti.MultiplicativeIdealWeight

variable {K : Type*} [Field K] [NumberField K] (χ : MultiplicativeIdealWeight K)

theorem TauCeti.MultiplicativeIdealWeight.logDeriv_LSeries_eq_neg_tsum_vonMangoldtTransform {s : ℂ}
    (hs : _root_.TauCeti.idealAbscissaOfAbsConv K χ.toIdealArithmeticFunction < s.re) :
    _root_.logDeriv (_root_.LSeries (_root_.TauCeti.normCoeff K χ.toIdealArithmeticFunction)) s
      = -∑' A : (_root_.Ideal (𝓞 K))⁰,
          _root_.TauCeti.idealTerm K χ.toIdealArithmeticFunction.vonMangoldtTransform s A := by sorry
