-- Prove2me | Theorems.Thm_QseriesFormalization_PartIV_Ch17_pentagonalMod5Minus_range
-- name    : QseriesFormalization.PartIV.Ch17.pentagonalMod5Minus_range
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T09:43:15.250621+00:00
-- url     : https://prove2.me/theorems/d2f95d4d-27c3-4cde-be1b-971e08d7b09a
-- title:
--   Minus-side pentagonal residues mod 5 lie in $\{0,1,2\}$
-- statement:
--   Define `pentagonalMod5Minus` on $\mathbb{Z}/5$ by $k\mapsto 3k(3k+4)$ (the residue of $k(3k-1)/2$ using $2^{-1}=3$). For every $k\in\mathbb{Z}/5$ its value is $0$, $1$ or $2$. A finite residue check in Chapter 17.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 17. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter17_PerTermAnalysis.lean#L110-L113

import Definitions.Def_QseriesFormalization_Chapter17_PerTermAnalysis
import Mathlib.Data.ZMod.Basic
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.Linarith

namespace QseriesFormalization.PartI.Ch04Franklin end QseriesFormalization.PartI.Ch04Franklin
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
open QseriesFormalization.PartIV
open QseriesFormalization.PartIV.Ch17

open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.PartI.Ch04Franklin

/-! ## Cast-to-ZMod-5 helpers for triangular and pentagonal residues -/

theorem QseriesFormalization.PartIV.Ch17.pentagonalMod5Minus_range : ∀ k : ZMod 5,
    pentagonalMod5Minus k = 0 ∨ pentagonalMod5Minus k = 1 ∨
    pentagonalMod5Minus k = 2 := by sorry
