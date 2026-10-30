-- Prove2me | Theorems.Thm_QseriesFormalization_PartIV_Ch19_jacobiTripleSign_triangular
-- name    : QseriesFormalization.PartIV.Ch19.jacobiTripleSign_triangular
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T09:55:25.983615+00:00
-- url     : https://prove2.me/theorems/e39df09d-6f45-4bb8-a794-dc524b044380
-- title:
--   $\mathrm{jacobiTripleSign}$ at triangular numbers
-- statement:
--   For every natural number $k$, $\mathrm{jacobiTripleSign}(k(k+1)/2)=(-1)^k(2k+1)$. Here $\mathrm{jacobiTripleSign}(n)$ is defined to be $(-1)^k(2k+1)$ if $n$ is the triangular number $k(k+1)/2$, and $0$ otherwise; it is the expected coefficient of $q^n$ in $(q;q)_\infty^3$ (Jacobi's identity). This statement checks the defining formula on triangular numbers (Chapter 19).
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 19. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter19_JacobiTripleSignChar.lean#L60-L83

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

theorem QseriesFormalization.PartIV.Ch19.jacobiTripleSign_triangular (k : ℕ) :
    jacobiTripleSign (k * (k + 1) / 2) = (-1 : ℤ) ^ k * (2 * k + 1) := by sorry
