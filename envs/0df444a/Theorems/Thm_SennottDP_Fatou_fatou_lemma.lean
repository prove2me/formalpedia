-- Prove2me | Theorems.Thm_SennottDP_Fatou_fatou_lemma
-- name    : SennottDP.Fatou.fatou_lemma
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T12:10:12.642642+00:00
-- url     : https://prove2.me/theorems/ea312497-e67d-4193-b882-3f584ffd5961
-- title:
--   Proposition A.2.1 (Fatou's Lemma) — for a probability distribution on a countable set, functions bounded below
-- statement:
--   Let $S$ be a countable set and $(P_j)_{j\in S}$ a probability distribution on $S$. Let $L\ge 0$ be a finite constant and let $u(j,N)$ take values in $[-L,\infty]$ for all $j\in S$ and all $N$. Then
--   $$\liminf_{N\to\infty}\ \sum_{j\in S} P_j\, u(j,N) \;\ge\; \sum_{j\in S} P_j\, \liminf_{N\to\infty} u(j,N), \tag{A.11}$$
--   with the convention $0\cdot\infty = 0$.
--
--   The lower bound $-L$ cannot be dropped (Example A.2.2). This is the tool for passing a limit inferior through an expectation over the next state.
--
--   **Formalization Note** $P_j\in[0,\infty]$ with $\sum_j P_j = 1$; $u$ is `EReal`-valued; each sum $\sum_j P_j u(j,\cdot)$ is the weighted sum `wsum` of the definition item, whose negative part is at most $L$, so it has a well-defined value in $(-\infty,\infty]$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 275, Proposition A.2.1, Eq. (A.11)

import Mathlib
import Definitions.Def_SennottDP_Fatou_Basic

open Filter Topology
open scoped ENNReal

namespace SennottDP.Fatou

/-- Sennott (1999), Proposition A.2.1 (Fatou's Lemma), p. 275, (A.11). `S` is countable,
`(P_j)_{j ∈ S}` is a probability distribution, and `u(j, N) ∈ [−L, ∞]` for a finite constant
`L ≥ 0`: `liminf_N ∑_j P_j u(j, N) ≥ ∑_j P_j liminf_N u(j, N)` (with `0 · ∞ = 0`). -/
theorem fatou_lemma {S : Type*} [Countable S] (P : S → ℝ≥0∞) (hP : ∑' j, P j = 1)
    (u : S → ℕ → EReal) (L : ℝ) (hL : 0 ≤ L) (hu : ∀ j N, ((-L : ℝ) : EReal) ≤ u j N) :
    wsum P (fun j => liminf (fun N => u j N) atTop) ≤
      liminf (fun N => wsum P (fun j => u j N)) atTop := by sorry

end SennottDP.Fatou
