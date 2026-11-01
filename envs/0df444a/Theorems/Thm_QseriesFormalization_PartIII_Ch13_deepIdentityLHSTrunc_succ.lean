-- Prove2me | Theorems.Thm_QseriesFormalization_PartIII_Ch13_deepIdentityLHSTrunc_succ
-- name    : QseriesFormalization.PartIII.Ch13.deepIdentityLHSTrunc_succ
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T09:11:31.047986+00:00
-- url     : https://prove2.me/theorems/d03353bc-70e1-4ba0-b928-922914dc7068
-- title:
--   Recursion for the truncated sum $\sum_{k\le N}q^{k^2}/(q;q)_k^2$
-- statement:
--   Let $R$ be a field, $q\in R$, $N\in\mathbb{N}$. Let $L_N(q)=\sum_{k=0}^{N}\dfrac{q^{k^2}}{(q;q)_k^2}$ be the $N$-th partial sum of the left-hand side of the Chapter 13 identity, where $(q;q)_k=\prod_{j=1}^k(1-q^j)$ (field division). Then
--   $$L_{N+1}(q)=L_N(q)+\frac{q^{(N+1)^2}}{(q;q)_{N+1}^{2}}.$$
--   This is the defining recursion of the partial sums, used for finite checks in Chapter 13.
--
--   Division uses Lean’s totalized field convention $a/0=0$. The statement or definition does not impose nonvanishing of its displayed denominators.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 13. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter13.lean#L36-L43

import Definitions.Def_QseriesFormalization_Chapter13
import Mathlib

/-!
# Chapter 13 — Chan's deep identity

⚠️  **SHADOW CHAPTER**.

Per `PLAYBOOK_AUDIT.md` (2026-05-22): this file currently contains only the
finite truncation `deepIdentityLHSTrunc q N := ∑_{k=0}^N q^{k²}/(q;q)_k²`
and closed-form unfoldings `deepIdentityLHSTrunc_zero..twenty`.  Chan's
Ch 13 main identity (the closed product form of `∑ q^{k²}/(q;q)_k²`,
related to the Andrews-Gordon family or Slater list) is **not**
formalized here — neither the LHS-RHS identity statement nor its proof.

Until a real chapter-main theorem is added, this file is auxiliary
scaffolding only.
-/

open QseriesFormalization
open QseriesFormalization.PartIII
open QseriesFormalization.PartIII.Ch13

variable {R : Type*} [Field R]

theorem QseriesFormalization.PartIII.Ch13.deepIdentityLHSTrunc_succ (q : R) (N : Nat) :
    deepIdentityLHSTrunc q (N + 1) =
      deepIdentityLHSTrunc q N +
        q ^ ((N + 1) * (N + 1)) / (qPochhammer q (N + 1)) ^ 2 := by sorry
