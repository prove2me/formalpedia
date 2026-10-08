-- Prove2me | Theorems.Thm_SchedComplexity_OneMachine_theorem_4e_equivalence
-- name    : SchedComplexity.OneMachine.theorem_4e_equivalence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:52:21.93337+00:00
-- url     : https://prove2.me/theorems/dd0be96d-bcdd-4a86-bbd3-8fc425b40c85
-- title:
--   Theorem 4(e) — KNAPSACK has a solution iff the constructed $n|1||\sum w_jU_j$ instance has $\sum w_jU_j\le A-b$
-- statement:
--   Let $a_1,\dots,a_t,b$ be positive integers with $0<b<A=\sum_{j\in T}a_j$. Consider the single-machine instance of reduction (e): $n=t$ jobs, all released at time $0$, with $p_{j1}=w_j=a_j$ and common due date $d_j=b$. Then
--
--   $$\exists\,S\subseteq T:\ \sum_{j\in S}a_j=b\quad\Longleftrightarrow\quad \exists\text{ feasible schedule with } \sum_{j\in T} w_jU_j\le A-b .$$
--
--   This is the equivalence behind KNAPSACK $\propto n|1||\sum w_jU_j$; the paper cites Karp and Figure 7 ($S$ in $[0,b]$, $T-S$ in $[b,A]$).
--
--   **Formalization Note** $0<b<A$ is the proof's standing assumption (p. 16); under it the threshold $A-b$ is a natural number. Idle time is allowed. The paper gives no argument beyond the construction; the statement makes the equivalence explicit.
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 19, Theorem 4(e)

import Mathlib
import Definitions.Def_SchedComplexity_OneMachine_Knapsack
import Definitions.Def_SchedComplexity_OneMachine_Constructions

namespace SchedComplexity.OneMachine

/-- Theorem 4(e), equivalence (Brucker, Lenstra & Rinnooy Kan, Report BW 43/75, p. 19): for
positive integers `a_1, …, a_t, b` with `0 < b < A = ∑ a_j`, KNAPSACK has a solution iff the
constructed `n|1||∑w_jU_j` instance (`p_{j1} = w_j = a_j`, `d_j = b`) has a feasible schedule
with `∑ w_j U_j ≤ y = A - b`. -/
theorem theorem_4e_equivalence (a : List ℕ) (b : ℕ) (ha : ∀ v ∈ a, 0 < v) (hb : 0 < b)
    (hbA : b < a.sum) :
    KnapsackYes a b ↔
      ∃ B, (instE a b).IsFeasible B ∧ (instE a b).sumWU B ≤ yE a b := by sorry

end SchedComplexity.OneMachine
