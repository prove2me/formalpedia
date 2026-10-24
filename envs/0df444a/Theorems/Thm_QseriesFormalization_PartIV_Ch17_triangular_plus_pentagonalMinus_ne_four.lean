-- Prove2me | Theorems.Thm_QseriesFormalization_PartIV_Ch17_triangular_plus_pentagonalMinus_ne_four
-- name    : QseriesFormalization.PartIV.Ch17.triangular_plus_pentagonalMinus_ne_four
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T09:46:33.494343+00:00
-- url     : https://prove2.me/theorems/62855189-514d-4052-890b-98f57ec15b37
-- title:
--   Residue obstruction: triangular + minus-side pentagonal $\not\equiv4\pmod5$
-- statement:
--   Let $k,j\in\mathbb{Z}/5$ with $2k+1\neq0$. Then `triangularMod5` $k$ + `pentagonalMod5Minus` $j$ $=3k(k+1)+3j(3j+4)\neq4$ in $\mathbb{Z}/5$. This is the minus-side counterpart of the plus-side obstruction in Chapter 17's mod 5 proof.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 17. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter17_PerTermAnalysis.lean#L115-L122

import Definitions.Def_QseriesFormalization_Chapter17_Mod5ResidueAnalysis
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

theorem QseriesFormalization.PartIV.Ch17.triangular_plus_pentagonalMinus_ne_four
    (k j : ZMod 5) (hk : (2 * k + 1 : ZMod 5) ≠ 0) :
    triangularMod5 k + pentagonalMod5Minus j ≠ 4 := by sorry
