-- Prove2me | Theorems.Thm_QseriesFormalization_PartII_Ch08_D_trunc_succ
-- name    : QseriesFormalization.PartII.Ch08.D_trunc_succ
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T09:27:38.321658+00:00
-- url     : https://prove2.me/theorems/73a9484a-5adc-49f3-b5e2-c634845230c0
-- title:
--   Recursion for the truncated series $D_N(q,a)=\sum_{n\le N}q^{n^2+an}/(q;q)_n$
-- statement:
--   Let $R$ be a field, $q\in R$ and $a,N\in\mathbb{N}$. Let $D_N(q,a)=\sum_{n=0}^{N}\dfrac{q^{n^2+an}}{(q;q)_n}$ be the $N$-th partial sum of the Chapter 8 series, where $(q;q)_n=\prod_{j=1}^n(1-q^j)$ (division is field division). Then
--   $$D_{N+1}(q,a)=D_N(q,a)+\frac{q^{(N+1)^2+a(N+1)}}{(q;q)_{N+1}}.$$
--   This is the defining recursion of the finite partial sums in Chapter 8 (a Rogers-Ramanujan-type family indexed by $a$).
--
--   Division uses Lean’s totalized field convention $a/0=0$. The statement or definition does not impose nonvanishing of its displayed denominators.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 8. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter08.lean#L53-L58

import Definitions.Def_QseriesFormalization_Chapter08
import Mathlib

/-!
# Chapter 8 — `D_n(q, a)` series

⚠️  **SHADOW CHAPTER**.

Per `PLAYBOOK_AUDIT.md` (2026-05-22): this file currently contains only the
finite truncation `D_partialSum q a N := ∑_{k=0}^N q^{k²+ak}/(q;q)_k` and
closed-form unfoldings `D_partialSum_zero..thirteen`.  Chan's Ch 8 main
identity for the `D_n(q, a)` series (the Bailey/Slater-type infinite-product
or theta-series representation as `N → ∞`) is **not** formalized here.

Until a real chapter-main theorem is added, this file is auxiliary
scaffolding only.
-/

open QseriesFormalization
open QseriesFormalization.PartII
open QseriesFormalization.PartII.Ch08

variable {R : Type*} [Field R]

theorem QseriesFormalization.PartII.Ch08.D_trunc_succ (q : R) (a : Nat) (N : Nat) :
    D_trunc q a (N + 1) =
      D_trunc q a N +
      q ^ ((N + 1) * (N + 1) + a * (N + 1)) / qPochhammer q (N + 1) := by sorry
