-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_Ch10MockThetaPS_ramanujanMockFPartialPS_zero
-- name    : QseriesFormalization.Pending.Ch10MockThetaPS.ramanujanMockFPartialPS_zero
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T10:54:15.167105+00:00
-- url     : https://prove2.me/theorems/a5d6505a-7532-4aaa-ba2a-6d7f470647b7
-- title:
--   The partial sum containing only the $n=0$ term of $f(q)$ equals $1$
-- statement:
--   Let $f_{\le N}$ denote the partial sum $\sum_{n=0}^{N}X^{n^2}\big((-X;X)_n^{-1}\big)^2$ in $\mathbb{Q}[[X]]$ (the truncation of the mock theta function $f(q)$ to summands $0,\dots,N$). Then $$f_{\le 0}=1.$$ Chapter 10 bookkeeping.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 10. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter10_MockTheta_PS.lean#L79-L83

import Definitions.Def_QseriesFormalization_Pending_Chapter10_MockTheta_PS
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.Linarith

namespace QseriesFormalization.PartII.Ch10 end QseriesFormalization.PartII.Ch10

/-!
# Chapter 10 / mock theta `f(q)` — formal power series foundation

⚠️  **AUX-LEVEL SCAFFOLDING** for what is currently a SHADOW chapter.

Ramanujan's third-order mock theta function (Lost Notebook):
  `f(q) := ∑_{n≥0} q^{n²} / (-q;q)_n²`.

The existing `Chapter10.ramanujanMockF_trunc` is the finite truncation;
this file defines `f(q)` as a *formal power series* `ramanujanMockFPS R`
(noncomputable, but well-defined coefficient-wise) and proves the basic
algebraic facts.  Chan §10's chapter-main result (Watson's identity, or
the mock-modular property) is not closed; this file lays the formal-PS
foundation toward such a closure.

## What this file contributes

- `ramanujanMockFPS R : PowerSeries R` over any commutative ring `R`,
  defined coefficient-wise via the truncations.
- `coeff_zero_ramanujanMockFPS = 1`: the `n = 0` term contributes `1`,
  higher-`n` terms contribute `0` to the constant coefficient.
- `ramanujanMockFPS_eq_coeff_trunc`: at the formal-PS level, each
  coefficient of `f(q)` equals the same coefficient of the finite
  truncation `ramanujanMockF_trunc q N` for any sufficiently-large `N`
  (the q-adic stabilisation argument).

## Approach to Chan §10 closure (open)

The chapter-main target is one of:
1. Watson's identity (1936): a closed form for `f(q)` in terms of theta
   series (the half-integral-weight cusp form / Eichler integral form).
2. The mock-modular property: `f(q)` has weight-1/2 mock-modular completion
   `\hat f(τ) = f(e^{2πiτ}) + (correction)` transforming as a modular form
   under `SL₂(ℤ)` (full proof needs Zwegers's holomorphic projection).
3. Andrews–Gordon–McIntosh order-3 mock theta identities.

All three are research-level (not in Hirschhorn either, per the
2026-05-24 subagent confirmation in `AUDIT_CLEANUP_PLAN.md`).
-/

open QseriesFormalization
open QseriesFormalization.Pending
open QseriesFormalization.Pending.Ch10MockThetaPS

open PowerSeries
open QseriesFormalization.PartII.Ch10

theorem QseriesFormalization.Pending.Ch10MockThetaPS.ramanujanMockFPartialPS_zero :
    ramanujanMockFPartialPS 0 = 1 := by sorry
