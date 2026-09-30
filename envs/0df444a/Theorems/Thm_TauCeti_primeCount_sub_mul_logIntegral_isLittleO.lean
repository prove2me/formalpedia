-- Prove2me | Theorems.Thm_TauCeti_primeCount_sub_mul_logIntegral_isLittleO
-- name    : TauCeti.primeCount_sub_mul_logIntegral_isLittleO
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:15:06.786707+00:00
-- url     : https://prove2.me/theorems/8bb77684-37cb-46b4-9e1c-1242fc00fcd7
-- title:
--   Transferring weighted prime asymptotics to ordinary counts
-- statement:
--   Let $K$ be a number field with ring of integers $\mathcal O_K$, and write $N(I)=|\mathcal O_K/I|$ for the norm of a nonzero integral ideal. For a set $S$ of nonzero prime ideals, put $\pi_S(x)=\#\{P\in S:N(P)\le x\}$ and $\vartheta_S(x)=\sum_{P\in S,\,N(P)\le x}\log N(P)$. Let $\delta\in\mathbb R$, and write $\operatorname{Li}(x)=\int_2^x(\log t)^{-1}\,dt$. If $\vartheta_S(x)-\delta x=o(x)$ at positive infinity, then
--
--   $$
--   \pi_S(x)-\delta\operatorname{Li}(x)=o\!\left(\frac{x}{\log x}\right)\qquad(x\to\infty).
--   $$
--
--   A linear asymptotic for the logarithmically weighted primes therefore yields the corresponding prime-number-theorem asymptotic.
--
--   Source and proof credit: the Tau Ceti contributors, [original declaration and proof](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/ArithmeticDirichletSeries/Transfer.lean#L104-L125), Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`; adapted to Lean 4.33.1.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/ArithmeticDirichletSeries/Transfer.lean#L104-L125

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_Analysis_SpecialFunctions_LogIntegral
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Counting
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Weight
import Definitions.Def_TauCeti_Order_Northcott_Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.InvLog
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Northcott
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
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
# From the weighted prime count to the unweighted one

A prime-number-theorem argument delivers its conclusion for a *logarithmically weighted* count: a
Tauberian theorem applied to a logarithmic derivative sees the von Mangoldt coefficients, hence the
count `ψ` weighted by `log p` and taken over prime powers, and a separate elementary estimate for
the prime-power contribution passes from `ψ` to the count `ϑ` over primes alone.  The statement one
wants is about the *unweighted* count `π`.  This file carries out that last passage for the primes
of a number field, taking the asymptotic for `ϑ` as given: if `ϑ(x) = δx + o(x)`, then
`π(x) = δ Li(x) + o(x/log x)`, where `Li` is the offset logarithmic integral of
`TauCeti/Analysis/SpecialFunctions/LogIntegral.lean`.

The bridge is the exact Abel-summation identity
`TauCeti.primeCount_eq_primeTheta_div_log_add_integral` of Layer 6.1 together with the
antiderivative identity `TauCeti.Real.logIntegral_eq_div_log_sub_add` for `Li`.  Subtracting the two
cancels the main terms and leaves
`TauCeti.primeCount_sub_mul_logIntegral_eq`, an identity valid for every `x ≥ 2` and every `δ`,
whose three remaining summands are each `o (x / log x)`.

## Main results

* `TauCeti.primeCount_sub_mul_logIntegral_eq`: the exact identity
  `π(x) - δ Li(x) = (ϑ(x) - δx)/log x + ∫ t in 2..x, (ϑ(t) - δt)/(t log² t) + 2δ/log 2`.
* `TauCeti.primeCount_sub_mul_logIntegral_isLittleO`: the transfer itself, stated so that it covers
  the density `δ = 0` as well.
* `TauCeti.primeCount_asymptotic_of_primeTheta`: the quotient form `ϑ(x) ∼ δx ⟹ π(x) ∼ δ Li(x)`
  for `δ ≠ 0`, and `TauCeti.primeCount_isLittleO_logIntegral` for the zero-density case, where an
  asymptotic equivalence would be false and the correct statement is `π(x) = o(Li x)`.

## Roadmap role

This is Layer **6.2** of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`, which asks for the
transfer `ϑ(x) ∼ δx ⟹ π(x) ∼ δ Li(x)` "including the zero-density and `δ = 0` cases"; Layer 10.3
exports it as `primeCount_asymptotic_of_primeTheta`.  Nothing here uses an analytic continuation or
a nonvanishing statement: the hypothesis on `ϑ` is taken as given here, and Layer 10 supplies it.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapter 1.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter I.2.

Mathlib's `Chebyshev.primeCounting_sub_theta_div_log_isBigO` performs the same partial-summation
step for the rational primes; the argument below follows it, and replaces its explicit Chebyshev
bound by the hypothesis on `ϑ`.
-/

 section

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

open Asymptotics Filter MeasureTheory
open scoped nonZeroDivisors NumberField
open IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ}

theorem TauCeti.primeCount_sub_mul_logIntegral_isLittleO
    (h : (fun x ↦ _root_.TauCeti.primeTheta K S x - δ * x) =o[_root_.Filter.atTop] _root_.id) :
    (fun x ↦ _root_.TauCeti.primeCount K S x - δ * _root_.TauCeti.Real.logIntegral x) =o[_root_.Filter.atTop] fun x : ℝ ↦ x / _root_.Real.log x := by sorry
