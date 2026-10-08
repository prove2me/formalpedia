-- Prove2me | Theorems.Thm_SchedComplexity_Tardiness_theorem_4d_equivalence
-- name    : SchedComplexity.Tardiness.theorem_4d_equivalence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T05:07:04.835542+00:00
-- url     : https://prove2.me/theorems/9b06216b-cbd1-4252-a6d8-e8fc5b8fd00e
-- title:
--   Theorem 4(d) — KNAPSACK has a solution iff the constructed instance has $\sum w_jT_j\le y$
-- statement:
--   Let $a_1,\dots,a_t$ be positive integers and $b$ an integer with $0<b<A$, where $A=\sum_{j=1}^t a_j$ and $a_*=\max_j a_j$ (the paper's standing assumption "we may assume that $0<b<A$", p. 16). Put
--
--   $$t'=\Big\lceil \tfrac12(t+1)(A-b)+\tfrac12\,t(t+1)a_*^2\Big\rceil ,$$
--
--   let $\tau$ be any integer with $\tau>2t'+A$, and consider the single-machine instance of Theorem 4(d) with $n=t+t'$ jobs: for $j\in T=\{1,\dots,t\}$, $p_j=\tau+a_j$, $w_j=\tau+a_j+1$, $d_j=t\tau+b$; for the $t'$ dummy jobs $j\notin T$, $p_j=\tau$, $w_j=\tau+1$, $d_j=t\tau+b$. Setting $a_j=0$ for $j\notin T$, every job has $p_j=\tau+a_j$ and $w_j=p_j+1$. The threshold is
--
--   $$y=\tfrac12\,t'(t'+1)\tau(\tau+1)+(t'+1)\tau(A-b)+t'.$$
--
--   For a processing order $\pi=(\pi(1),\dots,\pi(n))$ the jobs are processed without idle time from time $0$, so the job in position $j$ completes at $C_{\pi(j)}=\sum_{i\le j}p_{\pi(i)}$, and
--
--   $$c_\pi=C_{\pi(t)}-(t\tau+b).$$
--
--   Then KNAPSACK has a solution, i.e. $\sum_{j\in S}a_j=b$ for some $S\subseteq T$, if and only if the constructed instance of $n|1||\sum w_jT_j$ has a feasible schedule with
--
--   $$\sum_j w_jT_j\le y.$$
--
--   Schedules here are arbitrary feasible schedules (start times in $\mathbb N$, idle time allowed), not only schedules without idle time of processing orders. This is the equivalence of Theorem 4(d) (p. 20, "which proves the equivalence of KNAPSACK and this $n|1||\sum w_jT_j$ problem"); the goal theorem adds the polynomial-time computability of the construction.
--
--   **Formalization Note** The paper prints $t'=\tfrac12(t+1)(A-b)+\tfrac12t(t+1)a_*^2$, which is a half-integer when $(t+1)(A-b)$ is odd although $t'$ counts jobs; the Lean takes its ceiling (`tPrime`), and $y$ (`yThr`, an exact natural-number division since $t'(t'+1)$ is even) is computed from the same $t'$. Jobs are `Fin (t + t')`, the items of $T$ being the indices $0,\dots,t-1$ (`aExt` is the convention $a_j=0$ for $j\notin T$). Positions are 0-based in Lean: `π i` is the paper's $\pi(i+1)$, and `posCompletion p π k` is the paper's $C_{\pi(k)}$ for the 1-based position $k$ (the total processing time of the first $k$ positions). Sums $\sum_{j>t}$ run over the 0-based positions $i\ge t$ (`tailWeighted`). $\tau$ is quantified over all naturals with $\tau>2t'+A$, as in the paper.
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 20, proof of Theorem 4(d)

import Mathlib
import Definitions.Def_SchedComplexity_Tardiness_Construction
import Definitions.Def_SchedComplexity_Tardiness_Knapsack

namespace SchedComplexity.Tardiness

/-- The equivalence of Theorem 4(d), p. 20: for positive `a_1, …, a_t`, `0 < b < A` and every
`τ > 2t' + A`, KNAPSACK has a solution iff the constructed instance of `n|1||Σw_jT_j` has a
feasible schedule (arbitrary start times in `ℕ`, idle time allowed) with `Σ w_j T_j ≤ y`. -/
theorem theorem_4d_equivalence {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ)
    (ha : ∀ j, 0 < a j) (hb : 0 < b) (hbA : b < bigA a)
    (hτ : 2 * tPrime a b + bigA a < τ) :
    KnapsackYes a b ↔ HasScheduleLE (wtP a b τ) (wtW a b τ) (wtD a b τ) (yThr a b τ) := by sorry

end SchedComplexity.Tardiness
