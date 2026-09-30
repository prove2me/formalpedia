-- Prove2me | Theorems.Thm_TauCeti_MultiplicativeIdealWeight_hasDerivAt_tsum_prime_pow
-- name    : TauCeti.MultiplicativeIdealWeight.hasDerivAt_tsum_prime_pow
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:06:28.250043+00:00
-- url     : https://prove2.me/theorems/8cefdb65-bbe0-4760-805b-693db35c5ae2
-- title:
--   The prime-power expansion differentiates termwise
-- statement:
--   Let $K$ be a number field with ring of integers $\mathcal O_K$, and write $N(I)=|\mathcal O_K/I|$ for the norm of a nonzero integral ideal. Let $\chi$ be a completely multiplicative complex weight on integral ideals, preserving zero and one, with only finitely many zero values at nonzero prime ideals. Let $\sigma_a$ be the abscissa of absolute convergence of the ideal-indexed series of $\chi$, and put $F(z)=\sum_P\sum_{e\ge0}(\chi(P)N(P)^{-z})^{e+1}/(e+1)$. At every $s$ with $\operatorname{Re}s>\sigma_a$, the function $F$ is complex differentiable and
--
--   $$
--   F^{\prime}(s)=-\sum_P\sum_{e=0}^{\infty}\log N(P)\,(\chi(P)N(P)^{-s})^{e+1}.
--   $$
--
--   The logarithmic Euler expansion admits the indicated termwise derivative throughout its absolute-convergence half-plane.
--
--   Source and proof credit: the Tau Ceti contributors, [original declaration and proof](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/ArithmeticDirichletSeries/EulerProduct/Logarithm/Deriv.lean#L236-L275), Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`; adapted to Lean 4.33.1.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/ArithmeticDirichletSeries/EulerProduct/Logarithm/Deriv.lean#L236-L275

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Basic
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_EulerProduct_Data
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Regroup
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Weight
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Ring.Subgroup
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Module.Connected
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
# Derivatives of ideal Euler factors and logarithmic expansions

For general `TauCeti.EulerProductData`, this file first differentiates each local Euler factor.
The derivative at a prime `P` is the exact prime-power series

`-∑ e, log N(P ^ e) · D(P ^ e) / N(P ^ e) ^ s`.

This is the local analytic input for expressing the logarithmic derivative of a general ideal
Euler product in terms of its prime-power data. The second part of the file specializes to a
completely multiplicative weight, where the logarithm itself has a geometric Taylor expansion and
can be differentiated after summing over all primes and exponents.

`TauCeti.MultiplicativeIdealWeight.tsum_prime_pow_eq_tsum_neg_log_one_sub` expands the sum of local
logarithms over the prime powers `(P, e)`.  This file differentiates that expansion in `s`, term by
term, on the open half-plane where the ideal-indexed series converges absolutely.

Each term `(χ(P) N(P)⁻ˢ) ^ (e+1) / (e+1)` differentiates to `-log N(P) * (χ(P) N(P)⁻ˢ) ^ (e+1)`, so
the differentiated family is the undivided one weighted by `-log N(P)`.  Termwise differentiation of
a sum needs a summable majorant valid across a neighbourhood rather than at the single point, and
the half-plane supplies it: strictly to the right of a point of absolute convergence the weight
`log N(P)` is absorbed, which is `summable_log_absNorm_mul_norm_idealTerm_of_re_lt_re`, and the
exponent direction is geometric, which is `TauCeti.summable_mul_norm_pow_succ`.

`EulerProduct/Branch.lean` identifies the derivative of a *branch* of the logarithm with the
logarithmic derivative of the `L`-series.  That is an abstract identification; this file gives the
prime-power series the derivative is equal to.

## Main results

* `TauCeti.EulerProductData.hasDerivAt_eulerFactor`: a general local Euler factor differentiates
  termwise into the negative of its log-weighted prime-power series.
* `TauCeti.EulerProductData.logDeriv_eulerFactor_eq`: the local factor's logarithmic derivative is
  the negative quotient of that prime-power series by the local factor.
* `TauCeti.MultiplicativeIdealWeight.hasDerivAt_tsum_prime_pow`: the prime-power expansion
  differentiates termwise, strictly right of the abscissa of absolute convergence.
* `TauCeti.MultiplicativeIdealWeight.logDeriv_LSeries_eq_tsum_prime_pow`: that derivative **is**
  the logarithmic derivative of the `L`-series.
-/

 section

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

open Complex IsDedekindDomain

open scoped nonZeroDivisors NumberField

namespace TauCeti.EulerProductData
end TauCeti.EulerProductData
section EulerProductData
open TauCeti TauCeti.EulerProductData

open IdealArithmeticFunction

variable {K : Type*} [Field K] [NumberField K] (D : EulerProductData K)

/-! ### Derivative of a general local Euler factor -/











end EulerProductData

namespace TauCeti.MultiplicativeIdealWeight
end TauCeti.MultiplicativeIdealWeight
section MultiplicativeIdealWeight
open TauCeti TauCeti.MultiplicativeIdealWeight

open IdealArithmeticFunction

variable {K : Type*} [Field K] [NumberField K] (χ : MultiplicativeIdealWeight K)

theorem TauCeti.MultiplicativeIdealWeight.hasDerivAt_tsum_prime_pow {s : ℂ}
    (hs : _root_.TauCeti.idealAbscissaOfAbsConv K χ.toIdealArithmeticFunction < s.re) :
    _root_.HasDerivAt (fun z : ℂ ↦ ∑' pe : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K) × ℕ,
        (χ pe.1.asIdeal / (_root_.Ideal.absNorm pe.1.asIdeal : ℂ) ^ z) ^ (pe.2 + 1) / ((pe.2 : ℂ) + 1))
      (∑' pe : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K) × ℕ,
        -(_root_.Complex.log (_root_.Ideal.absNorm pe.1.asIdeal : ℂ)
          * (χ pe.1.asIdeal / (_root_.Ideal.absNorm pe.1.asIdeal : ℂ) ^ s) ^ (pe.2 + 1))) s := by sorry
