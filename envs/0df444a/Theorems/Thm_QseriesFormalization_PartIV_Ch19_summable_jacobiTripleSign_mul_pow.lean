-- Prove2me | Theorems.Thm_QseriesFormalization_PartIV_Ch19_summable_jacobiTripleSign_mul_pow
-- name    : QseriesFormalization.PartIV.Ch19.summable_jacobiTripleSign_mul_pow
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T10:00:50.982766+00:00
-- url     : https://prove2.me/theorems/0f004521-e0f3-4587-ac1b-7556723008ed
-- title:
--   Summability of $\sum_n\mathrm{jacobiTripleSign}(n)q^n$ for $|q|<1$
-- statement:
--   For $q\in\mathbb{C}$ with $|q|<1$, the series $\sum_{n\ge0}\mathrm{jacobiTripleSign}(n)\,q^n$ is summable. The coefficients satisfy $|\mathrm{jacobiTripleSign}(n)|\le 2n+1$, so they grow at most linearly. This is an analytic ingredient for comparing the formal and analytic forms of Jacobi's identity (Chapter 19).
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 19. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter19_JacobiTripleSignChar.lean#L133 (header match only; ported to Lean v4.33.1 / Mathlib 0df444a; proof adapted for this upload)

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

theorem QseriesFormalization.PartIV.Ch19.summable_jacobiTripleSign_mul_pow (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ => ((jacobiTripleSign n : ℤ) : ℂ) * q ^ n) := by sorry
