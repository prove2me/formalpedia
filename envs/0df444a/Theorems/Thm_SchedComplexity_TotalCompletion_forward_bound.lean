-- Prove2me | Theorems.Thm_SchedComplexity_TotalCompletion_forward_bound
-- name    : SchedComplexity.TotalCompletion.forward_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T14:09:16.564319+00:00
-- url     : https://prove2.me/theorems/af093b1e-1bdf-40f3-b6cf-8bf0d361b1a4
-- title:
--   Theorem 4(a), forward direction: the order $(S',S,J_n,T'-S',T-S,U)$ gives $\sum_jC_j\le y$
-- statement:
--   Let $a_1,\dots,a_t,b$ be positive integers with $0<b<A$, and suppose $S\subseteq T$ satisfies $\sum_{j\in S}a_j=b$. Put $S'=\{t+j\mid j\in T-S\}$. In the instance of the construction of Theorem 4(a), consider the processing order
--
--   $$\bigl(\{J_j\mid j\in S'\},\ \{J_j\mid j\in S\},\ J_n,\ \{J_j\mid j\in T'-S'\},\ \{J_j\mid j\in T-S\},\ \{J_j\mid j\in U\}\bigr),$$
--
--   with the jobs inside each group in any order, and the schedule it defines (each job starts as early as its release date and the previous job allow). Then this schedule is feasible and
--
--   $$\sum_{j\notin U}C_j\le u,\qquad \sum_{j\in U}C_j=u\sigma+\tfrac12u(u+1)\upsilon,\qquad \sum_j C_j\le y .$$
--
--   This is the "if" half of the equivalence behind Theorem 4(a).
--
--   **Formalization Note** The order inside each group is arbitrary: each group is given as a duplicate-free list whose set of elements is the group. The paper's displayed estimate $\sum_{j\notin U}C_j\le\dots=u$ is stated through its conclusion. Feasibility of the schedule, which the paper leaves implicit, is part of the conclusion.
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 22, proof of Theorem 4(a), forward direction

import Mathlib
import Definitions.Def_SchedComplexity_TotalCompletion_SingleMachine
import Definitions.Def_SchedComplexity_TotalCompletion_Construction

namespace SchedComplexity.TotalCompletion

/-- Proof of Theorem 4(a), forward direction (p. 22): if `Σ_{j∈S} a_j = b`, then the schedule of
the processing order `({J_j | j ∈ S'}, {J_j | j ∈ S}, J_n, {J_j | j ∈ T'−S'}, {J_j | j ∈ T−S},
{J_j | j ∈ U})`, with `S' = {t + j | j ∈ T−S}` and any order inside each group, is feasible and
has `Σ_{j∉U} C_j ≤ u`, `Σ_{j∈U} C_j = uσ + ½u(u + 1)υ` and `Σ_j C_j ≤ y`. -/
theorem forward_bound {t : ℕ} (a : Fin t → ℕ) (b : ℕ)
    (ha : ∀ i, 0 < a i) (hb : 0 < b) (hbA : b < sumA a)
    (S : Finset (Fin t)) (hS : ∑ i ∈ S, a i = b)
    (l₁ l₂ l₃ l₄ l₅ : List (Fin (numJobs a b)))
    (h₁ : l₁.Nodup ∧ l₁.toFinset = jobsShift a b Sᶜ)
    (h₂ : l₂.Nodup ∧ l₂.toFinset = jobsT a b S)
    (h₃ : l₃.Nodup ∧ l₃.toFinset = groupT' a b \ jobsShift a b Sᶜ)
    (h₄ : l₄.Nodup ∧ l₄.toFinset = jobsT a b Sᶜ)
    (h₅ : l₅.Nodup ∧ l₅.toFinset = groupU a b) :
    let B := orderSchedule (procTime a b) (release a b)
      (l₁ ++ l₂ ++ [lastJob a b] ++ l₃ ++ l₄ ++ l₅)
    IsFeasible (procTime a b) (release a b) B ∧
      ∑ j ∈ (groupU a b)ᶜ, completion (procTime a b) B j ≤ uCount a b ∧
      ∑ j ∈ groupU a b, completion (procTime a b) B j =
        uCount a b * sigma a b + uCount a b * (uCount a b + 1) / 2 * upsilon a b ∧
      ∑ j, completion (procTime a b) B j ≤ yThreshold a b := by sorry

end SchedComplexity.TotalCompletion
