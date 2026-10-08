-- Prove2me | Theorems.Thm_SchedComplexity_OneMachine_theorem_4f_equivalence
-- name    : SchedComplexity.OneMachine.theorem_4f_equivalence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:51:10.111994+00:00
-- url     : https://prove2.me/theorems/58ef8488-cabf-468b-b6d2-955267354dbc
-- title:
--   Theorem 4(f) — KNAPSACK has a solution iff the constructed $n|1|r_n\ge0,w_j=1|\sum w_jU_j$ instance has $\sum U_j\le0$
-- statement:
--   Let $a_1,\dots,a_t,b$ be positive integers with $0<b<A=\sum_{j\in T}a_j$, and take the instance of reductions (c) and (f): $n=t+1$ jobs with unit weights, the jobs $j\in T$ released at $0$ with $p_{j1}=a_j$, $d_j=A+1$, and the last job released at $r_n=b$ with $p_{n1}=1$, $d_n=b+1$. Then
--
--   $$\exists\,S\subseteq T:\ \sum_{j\in S}a_j=b\quad\Longleftrightarrow\quad \exists\text{ feasible schedule with } \sum_{j=1}^n w_jU_j\le 0 ,$$
--
--   that is, with no late job. This is the equivalence behind KNAPSACK $\propto n|1|r_n\ge0,w_j=1|\sum w_jU_j$ with threshold $y=0$; the paper states (c) and (f) with one construction.
--
--   **Formalization Note** As in (c), $0<b<A$ is the proof's standing assumption (p. 16), idle time is allowed, and the paper's "Cf. reduction (i) and Figure 4" is made explicit as this equivalence over all feasible schedules.
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 17, Theorem 4(f)

import Mathlib
import Definitions.Def_SchedComplexity_OneMachine_Knapsack
import Definitions.Def_SchedComplexity_OneMachine_Constructions

namespace SchedComplexity.OneMachine

/-- Theorem 4(f), equivalence (Brucker, Lenstra & Rinnooy Kan, Report BW 43/75, p. 17): for
positive integers `a_1, …, a_t, b` with `0 < b < A = ∑ a_j`, KNAPSACK has a solution iff the
constructed `n|1|r_n≥0,w_j=1|∑w_jU_j` instance (the construction of (c), unit weights) has a
feasible schedule with `∑ w_j U_j ≤ y = 0`. -/
theorem theorem_4f_equivalence (a : List ℕ) (b : ℕ) (ha : ∀ v ∈ a, 0 < v) (hb : 0 < b)
    (hbA : b < a.sum) :
    KnapsackYes a b ↔
      ∃ B, (instCF a b).IsFeasible B ∧ (instCF a b).sumWU B ≤ 0 := by sorry

end SchedComplexity.OneMachine
