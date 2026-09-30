-- Prove2me | Theorems.Thm_TauCeti_EulerProductData_LSeries_restrictAway_mul_prod_eulerFactor
-- name    : TauCeti.EulerProductData.LSeries_restrictAway_mul_prod_eulerFactor
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:12:39.942343+00:00
-- url     : https://prove2.me/theorems/3a36d4f6-c683-4c87-aa8a-8d33edc40af5
-- title:
--   Deleting finitely many Euler factors
-- statement:
--   Let $K$ be a number field with ring of integers $\mathcal O_K$, and write $N(I)=|\mathcal O_K/I|$ for the norm of a nonzero integral ideal. Let $D$ be complex coefficient data on the nonzero integral ideals, normalized by $D(\mathcal O_K)=1$ and multiplicative on relatively prime ideals. Write $L_D(s)=\sum_{n\ge1}a_D(n)n^{-s}$, where $a_D(n)=\sum_{N(I)=n}D(I)$. Let $S$ be a finite set of nonzero prime ideals, let $D^{(S)}$ agree with $D$ on ideals prime to $S$ and vanish elsewhere, and put $E_P(s)=\sum_{e\ge0}D(P^e)N(P)^{-es}$. If $\sum_{I\ne0}|D(I)N(I)^{-s}|<\infty$, then
--
--   $$
--   L_{D^{(S)}}(s)\prod_{P\in S}E_P(s)=L_D(s).
--   $$
--
--   This restores finitely many deleted local factors without requiring division by those factors.
--
--   Source and proof credit: the Tau Ceti contributors, [original declaration and proof](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/ArithmeticDirichletSeries/EulerProduct/Restrict.lean#L117-L139), Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`; adapted to Lean 4.33.1.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/ArithmeticDirichletSeries/EulerProduct/Restrict.lean#L117-L139

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Basic
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_EulerProduct_Analytic
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_EulerProduct_Basic
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_EulerProduct_Data
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_NormCoeff
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Regroup
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Weight
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_Ideal
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Ring.Subgroup
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Normed.Group.Tannery
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
# Deleting finitely many Euler factors

Restricting Euler-product data away from a finite set `S` of primes, keeping only the
coefficients of the ideals prime to `S`, replaces the local Euler factors at `S` by `1` and leaves
the others untouched. On the half-plane of absolute convergence the two `L`-series therefore
differ by the finitely many deleted factors; for a completely multiplicative weight `χ` the
restriction `χ.restrict S` divides the `L`-series by `∏ 𝔭 ∈ S, (1 - χ(𝔭) N(𝔭) ^ (-s))⁻¹`.

For the trivial weight the restriction is `ofBadPrimes S`, the indicator of the ideals prime to
`S`, and its `L`-series is the Dedekind zeta function with the Euler factors at `S` removed:

`L_S(s) = ζ_K(s) * ∏ 𝔭 ∈ S, (1 - N(𝔭) ^ (-s))`  for `Re s > 1`.

The correction factor does not vanish on `Re s > 0`, because
`|N(𝔭) ^ s| = N(𝔭) ^ (Re s) > 1` there. As `s → 1⁺`, the normalized expression
`(s - 1) L_S(s)` tends to `dedekindZeta_residue K` multiplied by the nonzero number
`∏ 𝔭 ∈ S, (1 - N(𝔭)⁻¹)`. The logarithmic derivative of `L_S` differs from that of `ζ_K` by the
finite sum `∑ 𝔭 ∈ S, log N(𝔭) / (N(𝔭) ^ s - 1)`, which is holomorphic on `Re s > 0` and in
particular across the line `Re s = 1`. This is the form in which Dirichlet series whose Euler
products omit the ramified primes, such as the trivial Galois-character series, are compared with
`ζ_K`.

## Main results

* `TauCeti.EulerProductData.eulerFactor_restrictAway_of_mem`,
  `TauCeti.EulerProductData.eulerFactor_restrictAway_of_notMem`: restricting away from `S`
  replaces the local factors at `S` by `1` and keeps the others.
* `TauCeti.EulerProductData.LSeries_restrictAway_mul_prod_eulerFactor`: multiplying the `L`-series
  of the restriction by the deleted local factors recovers the original `L`-series.
* `TauCeti.MultiplicativeIdealWeight.LSeries_restrict`: the same for a completely multiplicative
  weight, with the deleted factors in closed form.
* `TauCeti.LSeries_ofBadPrimes`: the `L`-series of the indicator of the ideals prime to `S` is
  `ζ_K(s) * ∏ 𝔭 ∈ S, (1 - N(𝔭) ^ (-s))` on `Re s > 1`.
* `TauCeti.prod_one_sub_absNorm_cpow_neg_ne_zero`: the correction factor has no zero on
  `Re s > 0`.
* `TauCeti.dedekindZeta_residue_mul_prod_one_sub_absNorm_cpow_neg_one_ne_zero`: the corrected
  residue at `s = 1` is nonzero.
* `TauCeti.tendsto_sub_one_mul_LSeries_ofBadPrimes`: the normalized right-hand limit at `s = 1`.
* `TauCeti.logDeriv_LSeries_ofBadPrimes`: the logarithmic derivative on `Re s > 1`, and
  `TauCeti.differentiableOn_sum_log_absNorm_div_cpow_sub_one`: the correction term in it is
  holomorphic on `Re s > 0`.
* `TauCeti.MultiplicativeIdealWeight.IsNormTwistOnGood.LSeries_normCoeff` and
  `TauCeti.MultiplicativeIdealWeight.IsNormTwistOnGood.tendsto_sub_one_mul_LSeries`: a weight that
  is a norm twist with parameter `u` on its good ideals has for `L`-series such a deleted zeta
  function read at `s - u * I`, with the corresponding pole at `s = 1 + u * I`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
-/

 section

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

open _root_.Filter
open scoped _root_.nonZeroDivisors _root_.NumberField _root_.Topology
open _root_.IsDedekindDomain (HeightOneSpectrum)

variable {K : Type*} [Field K] [NumberField K]

namespace TauCeti.EulerProductData
end TauCeti.EulerProductData
section EulerProductData
open TauCeti TauCeti.EulerProductData

variable (D : EulerProductData K) {s : ℂ}

theorem TauCeti.EulerProductData.LSeries_restrictAway_mul_prod_eulerFactor (S : _root_.Finset (_root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (hs : _root_.Summable (_root_.TauCeti.idealTerm K D.toIdealArithmeticFunction s)) :
    _root_.LSeries (_root_.TauCeti.normCoeff K (D.restrictAway S).toIdealArithmeticFunction) s *
        ∏ P ∈ S, D.eulerFactor P s =
      _root_.LSeries (_root_.TauCeti.normCoeff K D.toIdealArithmeticFunction) s := by sorry
