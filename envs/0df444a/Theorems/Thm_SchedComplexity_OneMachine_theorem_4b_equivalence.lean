-- Prove2me | Theorems.Thm_SchedComplexity_OneMachine_theorem_4b_equivalence
-- name    : SchedComplexity.OneMachine.theorem_4b_equivalence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:51:27.677886+00:00
-- url     : https://prove2.me/theorems/ca477c67-f612-4520-a8b0-531815dbd937
-- title:
--   Theorem 4(b) — KNAPSACK has a solution iff the constructed $n|1|L_{\max}\le0|\sum w_jC_j$ instance has value $\le y$
-- statement:
--   Let $a_1,\dots,a_t,b$ be positive integers with $0<b<A=\sum_{j\in T}a_j$. Consider the single-machine instance of reduction (b): $n=t+1$ jobs, all released at $0$; for $j\in T$, $p_{j1}=w_j=a_j$ and $d_j=A+1$; for the last job $p_{n1}=1$, $w_n=0$, $d_n=b+1$. Put
--
--   $$y=\sum_{j,k\in T,\ j\le k}a_ja_k+A-b .$$
--
--   Then KNAPSACK has a solution iff some feasible schedule meets every due date and has small weighted completion time:
--
--   $$\exists\,S\subseteq T:\ \sum_{j\in S}a_j=b\quad\Longleftrightarrow\quad \exists\text{ feasible schedule with } C_j\le d_j\ \forall j\ \text{ and }\ \sum_{j=1}^n w_jC_j\le y .$$
--
--   This is the equivalence behind KNAPSACK $\propto n|1|L_{\max}\le0|\sum w_jC_j$. The paper computes, for the processing order $(\{J_j\mid j\in S\},J_n,\{J_j\mid j\in T-S\})$, that $\sum w_jC_j=y-L_n\ge y$ with $L_n=\sum_{j\in S}a_j-b\le0$, and concludes "The equivalence follows immediately."
--
--   **Formalization Note** $0<b<A$ is the proof's standing assumption (p. 16). The double sum runs over ordered pairs of indices $j\le k$ (diagonal included). Schedules may contain idle time and any processing order; the paper's computation covers idle-free orders of the displayed shape, and the statement asserts the equivalence over all feasible schedules.
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 19, Theorem 4(b)

import Mathlib
import Definitions.Def_SchedComplexity_OneMachine_Knapsack
import Definitions.Def_SchedComplexity_OneMachine_Constructions

namespace SchedComplexity.OneMachine

/-- Theorem 4(b), equivalence (Brucker, Lenstra & Rinnooy Kan, Report BW 43/75, p. 19): for
positive integers `a_1, …, a_t, b` with `0 < b < A = ∑ a_j`, KNAPSACK has a solution iff the
constructed `n|1|L_max≤0|∑w_jC_j` instance has a feasible schedule meeting every due date
(`C_j ≤ d_j` for all `j`) with `∑ w_j C_j ≤ y = ∑_{j,k∈T, j≤k} a_j a_k + A - b`. -/
theorem theorem_4b_equivalence (a : List ℕ) (b : ℕ) (ha : ∀ v ∈ a, 0 < v) (hb : 0 < b)
    (hbA : b < a.sum) :
    KnapsackYes a b ↔
      ∃ B, (instB a b).IsFeasible B ∧ (∀ j, (instB a b).C B j ≤ (instB a b).d j) ∧
        (instB a b).sumWC B ≤ yB a b := by sorry

end SchedComplexity.OneMachine
