-- Prove2me | Theorems.Thm_QseriesFormalization_PartIV_Ch17_pentagonalSign_ne_zero_extract
-- name    : QseriesFormalization.PartIV.Ch17.pentagonalSign_ne_zero_extract
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T09:43:39.047297+00:00
-- url     : https://prove2.me/theorems/311086df-fe60-4c5a-9daf-e94787286597
-- title:
--   Extracting the pentagonal index from a nonzero pentagonal sign
-- statement:
--   `pentagonalSign` $\varepsilon(n)$ is $(-1)^k$ if $n=k(3k-1)/2$ for some $k$ (searched in $0..n$), else $(-1)^k$ if $n=k(3k+1)/2$ with $k>0$, else $0$ (the coefficient of $q^n$ in Euler's pentagonal series). The statement: if $\varepsilon(n)\neq0$ for $n\in\mathbb{N}$, then there is $k\le n$ with either $n=k(3k-1)/2$, or $0<k$ and $n=k(3k+1)/2$ (natural-number division), and $\varepsilon(n)=(-1)^k$. A technical witness-extraction lemma for Chapter 17.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 17. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter17_PerTermAnalysis.lean#L43-L74

import Definitions.Def_QseriesFormalization_Chapter05_Franklin
import Mathlib.Data.ZMod.Basic
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.Linarith

namespace QseriesFormalization.PartIV.Ch19 end QseriesFormalization.PartIV.Ch19

/-!
# Chapter 17 — Per-term mod-5 residue obstruction (helpers)

Helpers for closing the Finset.sum convolution sorry in
`Pending/Chapter17_Ramanujan5Conditional.lean`.

Strategy: when `jacobiTripleSign n ≠ 0`, the `List.find?` in its
definition returned `some k`, giving us `k ≤ n` with `n = k(k+1)/2`.
Similarly for `pentagonalSign`.

These extraction lemmas are the bridge from the existential structure
of `jacobiTripleSign` / `pentagonalSign` (defined via `find?`) to
explicit triangular / pentagonal indices, which the residue analysis
of `Chapter17_Mod5ResidueAnalysis` can then dispatch.
-/

open QseriesFormalization

open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.PartI.Ch04Franklin

theorem QseriesFormalization.PartIV.Ch17.pentagonalSign_ne_zero_extract (n : Nat) (h : pentagonalSign n ≠ 0) :
    ∃ k, k ≤ n ∧
      (n = k * (3 * k - 1) / 2 ∨ (0 < k ∧ n = k * (3 * k + 1) / 2)) ∧
      pentagonalSign n = (-1 : Int) ^ k := by sorry
