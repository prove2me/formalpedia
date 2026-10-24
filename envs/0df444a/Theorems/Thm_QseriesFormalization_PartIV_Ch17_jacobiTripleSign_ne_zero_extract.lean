-- Prove2me | Theorems.Thm_QseriesFormalization_PartIV_Ch17_jacobiTripleSign_ne_zero_extract
-- name    : QseriesFormalization.PartIV.Ch17.jacobiTripleSign_ne_zero_extract
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T09:34:22.672859+00:00
-- url     : https://prove2.me/theorems/ae3fee7e-aed9-4e4a-8d88-c72fbb2761f6
-- title:
--   Extracting the triangular index from a nonzero Jacobi sign coefficient
-- statement:
--   `jacobiTripleSign` $J(n)$ is $(-1)^k(2k+1)$ if $n=k(k+1)/2$ for some $k$ (searched among $0..n$), and $0$ otherwise (these are the coefficients of Jacobi's $\prod(1-q^m)^3$). The statement: for $n\in\mathbb{N}$ with $J(n)\neq0$, there exists $k\le n$ with $n=\lfloor k(k+1)/2\rfloor$ and $J(n)=(-1)^k(2k+1)$. A technical witness-extraction lemma for Chapter 17's per-term analysis.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 17. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter17_PerTermAnalysis.lean#L27-L41

import Definitions.Def_QseriesFormalization_DefCoreQSeries
import Mathlib.Data.ZMod.Basic
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.Linarith

namespace QseriesFormalization.PartI.Ch04Franklin end QseriesFormalization.PartI.Ch04Franklin

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
open QseriesFormalization.PartIV

open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.PartI.Ch04Franklin

theorem QseriesFormalization.PartIV.Ch17.jacobiTripleSign_ne_zero_extract (n : Nat) (h : jacobiTripleSign n ≠ 0) :
    ∃ k, k ≤ n ∧ n = k * (k + 1) / 2 ∧
      jacobiTripleSign n = (-1 : Int) ^ k * (2 * k + 1) := by sorry
