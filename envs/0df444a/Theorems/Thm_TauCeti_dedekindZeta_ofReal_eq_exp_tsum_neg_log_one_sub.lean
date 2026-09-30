-- Prove2me | Theorems.Thm_TauCeti_dedekindZeta_ofReal_eq_exp_tsum_neg_log_one_sub
-- name    : TauCeti.dedekindZeta_ofReal_eq_exp_tsum_neg_log_one_sub
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:11:56.274158+00:00
-- url     : https://prove2.me/theorems/6330af2f-542f-4130-9c05-aee0af92b249
-- title:
--   The real Euler product of the Dedekind zeta function in exponential form
-- statement:
--   Let $K$ be a number field with ring of integers $\mathcal O_K$, and write $N(I)=|\mathcal O_K/I|$ for the norm of a nonzero integral ideal. Let $\zeta_K$ be the Dedekind zeta function. For real $s>1$,
--
--   $$
--   \zeta_K(s)=\exp\!\left(\sum_{P\text{ prime}}-\log\bigl(1-N(P)^{-s}\bigr)\right).
--   $$
--
--   The formula expresses the real Euler product as an exponential of a convergent real sum.
--
--   Source and proof credit: the Tau Ceti contributors, [original declaration and proof](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/ArithmeticDirichletSeries/EulerProduct/Logarithm/DedekindZeta/Basic.lean), Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`; adapted to Lean 4.33.1.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/ArithmeticDirichletSeries/EulerProduct/Logarithm/DedekindZeta/Basic.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
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
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
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
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.DirichletDensity
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
# The real Euler product of the Dedekind zeta function in exponential form

For real `s > 1`, every local ratio `x = N(𝔭) ^ (-s)` of a height-one prime lies in `(0, 1/2]`,
because `N(𝔭) ≥ 2`. The principal logarithm of each Euler factor is then the real number
`-log (1 - x)`, and the exponential form
`TauCeti.MultiplicativeIdealWeight.exp_tsum_neg_log_one_sub_eq_LSeries` of the Euler product,
specialized to the trivial weight, becomes a statement about real numbers: `ζ_K(s)` is the
exponential of the convergent real sum `∑_𝔭 -log (1 - N(𝔭) ^ (-s))`. In particular `ζ_K(s)` is a
positive real number, and that sum is its real logarithm.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.absNorm_rpow_neg_le_half`: `N(𝔭) ^ (-s) ≤ 1/2`
  for `1 ≤ s`.
* `TauCeti.summable_neg_log_one_sub_absNorm_rpow`: `∑_𝔭 -log (1 - N(𝔭) ^ (-s))` converges for
  `1 < s`.
* `TauCeti.dedekindZeta_ofReal_eq_exp_tsum_neg_log_one_sub`: for real `s > 1`, `ζ_K(s)` is the
  exponential of that real sum.
* `TauCeti.dedekindZeta_re_eq_exp` and `TauCeti.dedekindZeta_re_pos`: the same for the real part,
  which is therefore positive.
* `TauCeti.log_dedekindZeta_re_eq_tsum_neg_log_one_sub`: that real sum is the real logarithm of
  `ζ_K(s)`.

## References

* The real logarithmic identity also appears, under the same name, in the
  Birkbeck–Brasca Chebotarev density project, <https://github.com/CBirkbeck/chebotarev-density>
  (Apache-2.0), commit `8575c9df1ae0a61120ab5c964c7911414254bec7`, file
  `CebotarevDensity/Density.lean`, where it is proved from `Real.hasProd_of_hasSum_log` and the
  product formula. It is derived here instead from TauCeti's exponential Euler product
  `TauCeti.MultiplicativeIdealWeight.exp_tsum_neg_log_one_sub_eq_LSeries`.
-/

 section

open _root_.IsDedekindDomain _root_.NumberField

namespace IsDedekindDomain.HeightOneSpectrum
end IsDedekindDomain.HeightOneSpectrum
section IsDedekindDomain.HeightOneSpectrum
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {K : Type*} [Field K] [NumberField K]



end IsDedekindDomain.HeightOneSpectrum

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

variable {K : Type*} [Field K] [NumberField K]

theorem TauCeti.dedekindZeta_ofReal_eq_exp_tsum_neg_log_one_sub {s : ℝ} (hs : 1 < s) :
    _root_.NumberField.dedekindZeta K s = (_root_.Real.exp (∑' P : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      -_root_.Real.log (1 - (_root_.Ideal.absNorm P.asIdeal : ℝ) ^ (-s))) : ℂ) := by sorry
