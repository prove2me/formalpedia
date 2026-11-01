-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_Ch11RRCFConvergent_rrcf_RPS_succ_diff_mul
-- name    : QseriesFormalization.Pending.Ch11RRCFConvergent.rrcf_RPS_succ_diff_mul
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T11:02:08.409887+00:00
-- url     : https://prove2.me/theorems/30fa285f-97a2-4040-a75c-9c299421e37a
-- title:
--   Successive $R$-convergent differences: $(R_{n+1}-R_n)A_nA_{n+1}=-(-1)^nX^{(n+1)(n+2)/2}$
-- statement:
--   For every $n\in\mathbb{N}$, in $\mathbb{Q}[[X]]$, with $R_n=B_nA_n^{-1}$ the Rogers--Ramanujan convergent, $$(R_{n+1}-R_n)\,A_n\,A_{n+1}=-(-1)^nX^{(n+1)(n+2)/2}.$$ Same rate as for $T_n$ but with opposite sign. Chapter 11.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 11. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter11_RRCF_Convergent.lean#L303-L328

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

/-! ## Formal-power-series version of the RRCF convergents

To talk about convergence `T_n → r(q)` as `n → ∞`, we lift the recurrence
from `ℂ → ℂ` to `ℚ⟦X⟧` (where the `X`-adic topology makes "stabilization
at fixed degree" precise). Each `B_n` has constant coefficient `1`, hence
is a unit, hence `T_n := A_n · B_n⁻¹` is a genuine formal power series.
-/

open PowerSeries

/-! ## Convergence-toward-`r(q)` infrastructure: the CF cross-determinant

The standard structural identity for CF convergents:
  `A_{n+1}·B_n − A_n·B_{n+1} = (−1)^n · X^{(n+1)(n+2)/2}`

drives the convergence of `T_n = A_n/B_n` in the X-adic topology of `ℚ⟦X⟧`,
because the difference `T_{n+1} − T_n = (−1)^n · X^{(n+1)(n+2)/2}/(B_n·B_{n+1})`
has X-adic order ≥ `(n+1)(n+2)/2 → ∞`, hence the sequence is Cauchy and
converges to a limit (`r(q)`, Chan Theorem 11.1).

We prove the cross-determinant identity by induction. -/

theorem QseriesFormalization.Pending.Ch11RRCFConvergent.rrcf_RPS_succ_diff_mul (n : ℕ) :
    (rrcf_RPS (n + 1) - rrcf_RPS n) * rrcf_APS n * rrcf_APS (n + 1)
      = -(((-1) ^ n : ℚ⟦X⟧) * X ^ ((n + 1) * (n + 2) / 2)) := by sorry
