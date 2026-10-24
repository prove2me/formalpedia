-- Prove2me | Theorems.Thm_QseriesFormalization_PartIV_Ch17_jacobiTripleSign_squared_per_term_zero_mod_7
-- name    : QseriesFormalization.PartIV.Ch17.jacobiTripleSign_squared_per_term_zero_mod_7
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T09:35:22.497021+00:00
-- url     : https://prove2.me/theorems/ca6a633b-16cc-485f-a8d6-5a576ece18c6
-- title:
--   Per-term vanishing mod 7: $J(i)J(j)\equiv0$ when $i+j=7n+5$
-- statement:
--   With `jacobiTripleSign` $J$ as above ($J(m)=(-1)^k(2k+1)$ for $m=k(k+1)/2$, else $0$), for all natural numbers $i,j,n$ with $i+j=7n+5$,
--   $$J(i)J(j)\equiv0\pmod 7.$$
--   This shows each term of the convolution giving the coefficient of $q^{7n+5}$ in $\prod(1-q^m)^6$ vanishes mod 7, a step in Chapter 17.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 17. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter17_Mod7PerTermAnalysis.lean#L118-L147

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
# Chapter 17 — Mod-7 per-term residue analysis for Ramanujan's 2nd congruence

For `i + j = 7n + 5`, `(jts i : ZMod 7) * (jts j : ZMod 7) = 0`.

Proof structure (analog of `Chapter17_PerTermAnalysis` for mod 5):
  - Triangular numbers mod 7 are in {0, 1, 3, 6}.
  - For `(jts i : ZMod 7) ≠ 0`: i is triangular AND its index is ≢ 3 mod 7,
    forcing `(i : ZMod 7) ∈ {0, 1, 3}`.
  - For pairs in `{0,1,3} × {0,1,3}`, the sum mod 7 ∈ {0,1,2,3,4,6} — never 5.
  - Hence convolution at 7n+5 is identically zero in ZMod 7.

This is the building block for `∀ n, 7 ∣ p(7n + 5)` via:
  `(qPochInfPS ZMod 7)^6 = (jacobiThetaPS ZMod 7)^2` (B2 squared) +
  `((jacobiThetaPS ZMod 7)^2).coeff (7n+5) = 0` (this analysis) +
  `ramanujan_from_pochInf_vanishes 7`.
-/

open QseriesFormalization
open QseriesFormalization.PartIV

open QseriesFormalization.PartIV.Ch19

theorem QseriesFormalization.PartIV.Ch17.jacobiTripleSign_squared_per_term_zero_mod_7 (i j n : ℕ)
    (h_sum : i + j = 7 * n + 5) :
    ((jacobiTripleSign i : ℤ) : ZMod 7) *
      ((jacobiTripleSign j : ℤ) : ZMod 7) = 0 := by sorry
