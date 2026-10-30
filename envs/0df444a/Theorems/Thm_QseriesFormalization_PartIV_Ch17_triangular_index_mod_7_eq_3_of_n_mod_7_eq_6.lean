-- Prove2me | Theorems.Thm_QseriesFormalization_PartIV_Ch17_triangular_index_mod_7_eq_3_of_n_mod_7_eq_6
-- name    : QseriesFormalization.PartIV.Ch17.triangular_index_mod_7_eq_3_of_n_mod_7_eq_6
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T09:45:55.620814+00:00
-- url     : https://prove2.me/theorems/c6ea9792-d83d-4d58-852a-0f9e1080314d
-- title:
--   Triangular numbers $\equiv6\pmod 7$ have index $\equiv3\pmod 7$
-- statement:
--   Let $n,k\in\mathbb{N}$ with $n=\lfloor k(k+1)/2\rfloor$ (natural-number division) and $n\equiv 6\pmod 7$ (in $\mathbb{Z}/7$). Then $k\equiv3\pmod 7$. A residue lemma for Chapter 17's mod 7 analysis.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 17. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter17_Mod7PerTermAnalysis.lean#L68-L86

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

namespace QseriesFormalization.PartIV.Ch19 end QseriesFormalization.PartIV.Ch19

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

open QseriesFormalization.PartIV.Ch19

theorem QseriesFormalization.PartIV.Ch17.triangular_index_mod_7_eq_3_of_n_mod_7_eq_6 (n k : ℕ)
    (heq : n = k * (k + 1) / 2) (hn : (n : ZMod 7) = 6) :
    (k : ZMod 7) = 3 := by sorry
