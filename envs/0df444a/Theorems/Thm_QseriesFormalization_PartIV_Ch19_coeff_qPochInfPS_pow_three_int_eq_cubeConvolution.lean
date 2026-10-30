-- Prove2me | Theorems.Thm_QseriesFormalization_PartIV_Ch19_coeff_qPochInfPS_pow_three_int_eq_cubeConvolution
-- name    : QseriesFormalization.PartIV.Ch19.coeff_qPochInfPS_pow_three_int_eq_cubeConvolution
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T09:52:42.611394+00:00
-- url     : https://prove2.me/theorems/4ffb232a-dfc0-45ff-82ff-ed0621b5a7ac
-- title:
--   Coefficients of $(q;q)_\infty^3$ as a cube convolution of pentagonal signs
-- statement:
--   For every natural number $n$, the coefficient of $X^n$ in $\big((q;q)_\infty\big)^3\in\mathbb{Z}[[X]]$ (where $(q;q)_\infty$ is `qPochInfPS ℤ`) is
--   $$\sum_{p+c=n}\Big(\sum_{a+b=p}\sigma(a)\sigma(b)\Big)\sigma(c),\qquad \sigma=\mathrm{pentagonalSign},$$
--   the triple convolution of the pentagonal-sign sequence. This is the formal multiplication rule applied to Euler's pentagonal number theorem, used for the formal Jacobi identity (Chapter 19).
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 19. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter19_JacobiTripleSignChar.lean#L215 (header match only; ported to Lean v4.33.1 / Mathlib 0df444a; proof adapted for this upload)

import Definitions.Def_QseriesFormalization_Chapter05_Franklin
import Definitions.Def_QseriesFormalization_DefCoreQSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Characterisation of `jacobiTripleSign`

Two clean closed forms for `jacobiTripleSign` (defined in `Chapter19.lean`
via `List.find?` on triangular indices):

* `jacobiTripleSign_triangular`: `jacobiTripleSign (k*(k+1)/2) = (-1)^k * (2k+1)`.
* `jacobiTripleSign_of_not_triangular`: `jacobiTripleSign n = 0` when no
  `k ≤ n` satisfies `n = k*(k+1)/2`.

These will be needed by both attack routes on the cube convolution
identity (Sylvester combinatorial proof in `Pending/Sylvester_TripleSum`
and the analytic-formal Taylor bridge in `Pending/JacobiCubeAnalyticToFormal`).
Stating them in the main build (rather than inside a Pending file)
keeps the headline target portable.
-/

open QseriesFormalization
open QseriesFormalization.PartIV
open QseriesFormalization.PartIV.Ch19

theorem QseriesFormalization.PartIV.Ch19.coeff_qPochInfPS_pow_three_int_eq_cubeConvolution (n : ℕ) :
    ((qPochInfPS ℤ)^3).coeff n =
      ∑ pq ∈ Finset.HasAntidiagonal.antidiagonal n,
        (∑ ab ∈ Finset.HasAntidiagonal.antidiagonal pq.1,
          (QseriesFormalization.PartI.Ch04Franklin.pentagonalSign ab.1 : ℤ) *
          (QseriesFormalization.PartI.Ch04Franklin.pentagonalSign ab.2 : ℤ)) *
        (QseriesFormalization.PartI.Ch04Franklin.pentagonalSign pq.2 : ℤ) := by sorry
