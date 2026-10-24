-- Prove2me | Theorems.Thm_QseriesFormalization_PartIV_Ch17_triangular_cast_eq_triangularMod5
-- name    : QseriesFormalization.PartIV.Ch17.triangular_cast_eq_triangularMod5
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T09:45:50.844815+00:00
-- url     : https://prove2.me/theorems/702f06d0-e6eb-4c23-97f1-ca5ec0738bf4
-- title:
--   Cast of $k(k+1)/2$ to $\mathbb{Z}/5$ equals `triangularMod5`
-- statement:
--   For every $k\in\mathbb{N}$, the natural number $\lfloor k(k+1)/2\rfloor$ cast to $\mathbb{Z}/5$ equals `triangularMod5` of $k$ cast to $\mathbb{Z}/5$, where `triangularMod5` $x=3x(x+1)$. It links actual triangular numbers to the residue model in Chapter 17.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 17. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter17_PerTermAnalysis.lean#L78-L103

import Definitions.Def_QseriesFormalization_Chapter17_Mod5ResidueAnalysis
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

theorem QseriesFormalization.PartIV.Ch17.triangular_cast_eq_triangularMod5 (k : Nat) :
    ((k * (k + 1) / 2 : ℕ) : ZMod 5) = triangularMod5 (k : ZMod 5) := by sorry
