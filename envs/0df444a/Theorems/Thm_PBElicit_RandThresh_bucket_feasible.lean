-- Prove2me | Theorems.Thm_PBElicit_RandThresh_bucket_feasible
-- name    : PBElicit.RandThresh.bucket_feasible
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T06:49:53.47752+00:00
-- url     : https://prove2.me/theorems/d6875db7-00d4-4cd8-9bda-cfd8b4349431
-- title:
--   Proof of Theorem 3.5, p. 13 — at most 1/u_j alternatives from bucket S_j fit in the budget
-- statement:
--   Let $m=2^K$ be the number of alternatives, with costs $c_a$, and let $S_j=\{a: c_a\in I_j\}$ be the cost bucket for $0\le j\le 2\log_2 m$, where $I_0=[0,1/m^2]$, $I_j=(2^{j-1}/m^2,2^j/m^2]$ and $u_j=2^j/m^2$. If $S\subseteq S_j$ and $|S|\le 1/u_j$, then
--   $$
--   c(S)=\sum_{a\in S}c_a\ \le\ 1 .
--   $$
--   This is what lets Mechanism A pick up to $1/u_k$ alternatives from one bucket without violating the budget.
--
--   **Formalization Note.** $m$ is `Fintype.card A` $=2^K$; the cardinality bound is the real inequality $|S|\le 1/u_j$.
-- source:
--   Benadè, Nath, Procaccia & Shah, Preference Elicitation for Participatory Budgeting, author's manuscript (2018; Manag. Sci. 2021, doi:10.1287/mnsc.2020.3666), proof of Theorem 3.5, p. 13, "Note that selecting at most 1/u_j alternatives from S_j is guaranteed to satisfy the budget constraint"

import Mathlib
import Definitions.Def_PBElicit_RandThresh_Setting

namespace PBElicit.RandThresh

theorem bucket_feasible {A : Type*} [Fintype A] (c : A → ℝ) (m K : ℕ)
    (hA : Fintype.card A = m) (hmK : m = 2 ^ K) (j : ℕ) (hj : j ≤ 2 * K) (S : Finset A)
    (hS : S ⊆ bucket c m j) (hcard : (S.card : ℝ) ≤ 1 / up m j) :
    cost c S ≤ 1 := by sorry

end PBElicit.RandThresh
