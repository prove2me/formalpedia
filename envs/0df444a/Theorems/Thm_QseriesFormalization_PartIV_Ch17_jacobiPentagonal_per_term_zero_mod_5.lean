-- Prove2me | Theorems.Thm_QseriesFormalization_PartIV_Ch17_jacobiPentagonal_per_term_zero_mod_5
-- name    : QseriesFormalization.PartIV.Ch17.jacobiPentagonal_per_term_zero_mod_5
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T09:34:23.536978+00:00
-- url     : https://prove2.me/theorems/e2141301-3ecc-4ba0-a36d-7cb95f5aea74
-- title:
--   Per-term vanishing mod 5: $J(i)\,\varepsilon(j)\equiv0$ when $i+j=5m+4$
-- statement:
--   Let $J$ = `jacobiTripleSign` ($J(n)=(-1)^k(2k+1)$ if $n=k(k+1)/2$, else $0$) and $\varepsilon$ = `pentagonalSign` (the sign $(-1)^k$ of $q^n$ in Euler's pentagonal series $\prod(1-q^m)$, and $0$ if $n$ is not pentagonal). For all natural numbers $i,j,m$ with $i+j=5m+4$,
--   $$J(i)\,\varepsilon(j)\equiv 0 \pmod 5$$
--   (in $\mathbb{Z}/5$). Every term of the convolution for the coefficient of $q^{5m+4}$ vanishes mod 5, which is the per-term core of Chapter 17's proof of $p(5n+4)\equiv0\pmod5$.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 17. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter17_PerTermAnalysis.lean#L187-L261

import Definitions.Def_QseriesFormalization_Chapter05_Franklin
import Definitions.Def_QseriesFormalization_DefCoreQSeries
import Mathlib.Data.ZMod.Basic
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.Linarith

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

/-! ## Cast-to-ZMod-5 helpers for triangular and pentagonal residues -/

theorem QseriesFormalization.PartIV.Ch17.jacobiPentagonal_per_term_zero_mod_5
    (i j m : Nat) (h_sum : i + j = 5 * m + 4) :
    ((jacobiTripleSign i : ℤ) : ZMod 5) *
      ((QseriesFormalization.PartI.Ch04Franklin.pentagonalSign j : ℤ) : ZMod 5) = 0 := by sorry
