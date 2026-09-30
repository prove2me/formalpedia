-- Prove2me | Theorems.Thm_TauCeti_UnitaryIdealWeight_norm_LSeries_threeFourOne_ge_one
-- name    : TauCeti.UnitaryIdealWeight.norm_LSeries_threeFourOne_ge_one
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:12:59.966811+00:00
-- url     : https://prove2.me/theorems/67058b29-7d1a-4b14-97f9-facc8327bf0d
-- title:
--   The 3-4-1 bound for unitary ideal weights
-- statement:
--   Let $K$ be a number field with ring of integers $\mathcal O_K$, and write $N(I)=|\mathcal O_K/I|$ for the norm of a nonzero integral ideal. Let $\chi$ be a unitary ideal weight: it is completely multiplicative, vanishes at only finitely many nonzero prime ideals, and has modulus one on every other nonzero prime ideal. Let $\chi_0$ be a completely multiplicative ideal weight, equal to one on nonzero ideals avoiding its finite set $B_0$ of zero prime values. Suppose every prime in $B_0$ is also a zero prime of $\chi$. For any weight $\eta$, let $L_\eta(s)=\sum_{I\ne0}\eta(I)N(I)^{-s}$ in its region of absolute convergence. For real $\sigma>1$ and $t\in\mathbb R$,
--
--   $$
--   \left|L_{\chi_0}(\sigma)^3L_\chi(\sigma+it)^4L_{\chi^2}(\sigma+2it)\right|\ge1.
--   $$
--
--   This three-factor lower bound is the classical $3$–$4$–$1$ inequality for ideal Euler products.
--
--   Source and proof credit: the Tau Ceti contributors, [original declaration and proof](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/ArithmeticDirichletSeries/EulerProduct/ThreeFourOne.lean#L101-L138), Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`; adapted to Lean 4.33.1.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/ArithmeticDirichletSeries/EulerProduct/ThreeFourOne.lean#L101-L138

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
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Ring.Subgroup
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.LinearAlgebra.Pi
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.NumberTheory.LSeries.Convolution
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
# The 3-4-1 bound for the Euler products of unitary ideal weights

Let `χ` be a unitary ideal weight of a number field `K`, and let `χ₀` be a weight that is trivial
on its good ideals and whose bad primes are among those of `χ` — for instance the trivial weight,
whose `L`-series is the Dedekind zeta function `ζ_K`. For real `σ > 1` and real `t`, this file
proves the classical `3-4-1` inequality

```text
1 ≤ ‖L(χ₀, σ) ^ 3 * L(χ, σ + it) ^ 4 * L(χ², σ + 2it)‖,
```

where each `L`-series is the `LSeries` of the norm coefficients of the weight. It is the
positivity input for nonvanishing on the line `Re s = 1`, and is exactly the bound hypothesis of
the analytic criterion `TauCeti.LSeries.ne_zero_of_threeFourOne`: a continuation of `L(χ, ·)`
that is differentiable at `1 + it` does not vanish there, provided `L(χ₀, σ) = O((σ - 1)⁻¹)` as
`σ → 1⁺` and `L(χ², ·)` continues continuously to `1 + 2it`.

## Main results

* `TauCeti.UnitaryIdealWeight.norm_LSeries_threeFourOne_ge_one`: the `3-4-1` bound for a unitary
  weight `χ` against a weight `χ₀` trivial on its good ideals, with bad primes among those of `χ`.
* `TauCeti.UnitaryIdealWeight.norm_dedekindZeta_threeFourOne_ge_one`: the case `χ₀ = 1`, where the
  first factor is the Dedekind zeta function.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapter 4.
* The global argument is that of Mathlib's `DirichletCharacter.norm_LSeries_product_ge_one` in
  `Mathlib/NumberTheory/LSeries/Nonvanishing.lean`, by Michael Stoll and David Loeffler, with
  unitary ideal weights of a number field in place of Dirichlet characters.
-/

 section

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

open Complex IsDedekindDomain NumberField

variable {K : Type*} [Field K] [NumberField K]

namespace TauCeti.UnitaryIdealWeight
end TauCeti.UnitaryIdealWeight
section UnitaryIdealWeight
open TauCeti TauCeti.UnitaryIdealWeight

variable {χ₀ : MultiplicativeIdealWeight K}

theorem TauCeti.UnitaryIdealWeight.norm_LSeries_threeFourOne_ge_one (χ : _root_.TauCeti.UnitaryIdealWeight K)
    (h₀ : χ₀.IsTrivialOnGood) (hbad : χ₀.badPrimes ⊆ χ.1.badPrimes) {σ : ℝ} (hσ : 1 < σ)
    (t : ℝ) :
    1 ≤ ‖_root_.LSeries (_root_.TauCeti.normCoeff K χ₀.toIdealArithmeticFunction) σ ^ 3 *
      _root_.LSeries (_root_.TauCeti.normCoeff K χ.toIdealArithmeticFunction) ((σ : ℂ) + _root_.Complex.I * t) ^ 4 *
      _root_.LSeries (_root_.TauCeti.normCoeff K (χ ^ 2).toIdealArithmeticFunction) ((σ : ℂ) + 2 * _root_.Complex.I * t)‖ := by sorry
