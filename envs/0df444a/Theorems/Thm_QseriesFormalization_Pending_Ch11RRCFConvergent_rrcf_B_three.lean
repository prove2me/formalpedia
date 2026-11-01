-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_Ch11RRCFConvergent_rrcf_B_three
-- name    : QseriesFormalization.Pending.Ch11RRCFConvergent.rrcf_B_three
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T11:00:28.220244+00:00
-- url     : https://prove2.me/theorems/209ba9d1-b02a-4373-ba65-ff62d6bccbbd
-- title:
--   Denominator $B_3(q)=1+q^2+q^3$ (scalar version)
-- statement:
--   For every $q\in\mathbb{C}$, with $B_0=B_1=1$, $B_{n+2}=B_{n+1}+q^{n+2}B_n$, $$B_3(q)=1+q^2+q^3.$$ Chapter 11.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 11. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter11_RRCF_Convergent.lean#L91-L94

import Definitions.Def_QseriesFormalization_Pending_Chapter11_RRCF_Convergent
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.Linarith

/-!
# Chapter 11 — Rogers-Ramanujan continued fraction: correct convergents

⚠️ **AUX-LEVEL SCAFFOLDING** for Ch11 (currently AUX).

`Chapter11.R_trunc` builds the RRCF "outside-in" with `q^k` on the *outer*
factor at step `k`, which makes `R_trunc q n → 1` trivially as `n → ∞`
(since `q^n → 0` for `|q| < 1`).  That truncation is NOT a convergent of
the true RRCF.

This file defines the **standard convergents** of

  `R(q) = q^{1/5} · 1 / (1 + q / (1 + q² / (1 + q³ / (⋯))))`

via the **backward recurrence** for continued-fraction convergents
`p_n = a_n·p_{n-1} + b_n·p_{n-2}` with `a_n = 1`, `b_n = q^n`, and the
"trivial 0-th convergent = 1" initial condition `(p_{-1}=1, p_0=1)`, giving

  `p_0 = 1,  p_1 = 1 + q,  p_{n+1} = p_n + q^{n+1}·p_{n-1}`
  `q_0 = 1,  q_1 = 1,      q_{n+1} = q_n + q^{n+1}·q_{n-1}`

The `n`-th convergent (stripped of the `q^{1/5}` prefactor) is
`T_n(q) := p_n(q) / q_n(q)`; numerically `T_n → r(q) = (q;q^5)(q^4;q^5)/((q^2;q^5)(q^3;q^5))`
(Chan Theorem 11.1).

## What this file contributes (corrected 2026-05-27)

Note: yesterday's commit of this file had a base-case bug (`rrcf_A 1 := 1`
instead of `1+q`, `rrcf_B 0 := 0` instead of `1`) that made the recurrence
compute a different CF. Today's version is the corrected one matching
Chan §11 / Theorem 11.1.

- `rrcf_A`, `rrcf_B` : ℕ → ℂ → ℂ definitions, scalar form, for the
  numerator / denominator convergent sequences.
- `rrcf_APS`, `rrcf_BPS` : ℕ → ℚ⟦X⟧ formal-PS lift.
- `rrcf_TPS n := rrcf_APS (n+1) * (rrcf_BPS (n+1))⁻¹` formal-PS convergent.
- Small explicit values + base-case lemmas.

The chapter-main result (X-adic convergence of `rrcf_TPS n` to the formal
power series `r(q)`, equivalent to Chan Theorem 11.1) remains open; this
file provides the correct combinatorial scaffolding.
-/

open QseriesFormalization
open QseriesFormalization.Pending
open QseriesFormalization.Pending.Ch11RRCFConvergent

theorem QseriesFormalization.Pending.Ch11RRCFConvergent.rrcf_B_three (q : ℂ) : rrcf_B 3 q = 1 + q ^ 2 + q ^ 3 := by sorry
