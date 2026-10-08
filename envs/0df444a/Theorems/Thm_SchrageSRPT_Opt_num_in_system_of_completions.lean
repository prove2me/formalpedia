-- Prove2me | Theorems.Thm_SchrageSRPT_Opt_num_in_system_of_completions
-- name    : SchrageSRPT.Opt.num_in_system_of_completions
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:22:37.312503+00:00
-- url     : https://prove2.me/theorems/439f4a56-775c-47c5-ba04-062802672f93
-- title:
--   PROOF, p. 689 — from (1)–(3): N_r(y) = N_o(y) − 1 for C_r(j) ≤ y < min[C_o(k), C_o(j)], and N_r(y) = N_o(y) otherwise
-- statement:
--   Let $\delta_o$ and $\delta_r$ be two schedules of the same arrival stream, in which only finitely many jobs arrive by any given time. Let $j \ne k$ be jobs such that
--
--   1. $C_o(i) = C_r(i)$ for every $i \ne j, k$;
--   2. $\min[C_r(k), C_r(j)] < \min[C_o(k), C_o(j)]$;
--   3. $\max[C_r(k), C_r(j)] = \max[C_o(k), C_o(j)]$;
--
--   and $j$ is the first of the two to complete under $\delta_r$: $C_r(j) \le C_r(k)$. Then for every time $y$,
--   $$N_r(y) = N_o(y) - 1 \quad\text{if } C_r(j) \le y < \min[C_o(k), C_o(j)], \qquad N_r(y) = N_o(y) \quad\text{otherwise}.$$
--
--   This is the counting step of the letter's PROOF: it turns relations (1)–(3) on completion times into a comparison of the numbers of jobs in system, showing that the revised schedule has at most as many jobs in system at every time.
--
--   **Formalization Note.** The letter writes the interval as $C_r(j) \le y \le \min[C_o(k), C_o(j)]$. At $y = \min[C_o(k), C_o(j)]$ the job completing then under $\delta_o$ has already left the system (a job is in system on $[A(n), C(n))$), so the two counts are equal there; the statement uses the half-open interval. The difference is written $N_r(y) + 1 = N_o(y)$ in natural numbers. Local finiteness of arrivals is added so that $N$ is a genuine count. Completion times take values in $\mathbb R \cup \{+\infty\}$.
-- source:
--   Schrage, A proof of the optimality of the shortest remaining processing time discipline, Oper. Res. 16 (1968), p. 689, PROOF, relations (1)–(3) and the sentence "Thus, N_r(y) = N_o(y) − 1 for C_r(j) ≦ y ≦ min[C_o(k), C_o(j)], and N_r(y) = N_o(y) otherwise"

import Mathlib
import Definitions.Def_SchrageSRPT_Opt_Model

namespace SchrageSRPT.Opt
theorem num_in_system_of_completions (A P : ℕ → ℝ) (hfin : ∀ t : ℝ, {n | A n ≤ t}.Finite)
    (δo δr : ℕ → ℝ → ℝ) (hδo : IsSchedule A δo) (hδr : IsSchedule A δr)
    (j k : ℕ) (hjk : j ≠ k)
    (h1 : ∀ i, i ≠ j → i ≠ k → completion A P δo i = completion A P δr i)
    (h2 : min (completion A P δr k) (completion A P δr j) <
      min (completion A P δo k) (completion A P δo j))
    (h3 : max (completion A P δr k) (completion A P δr j) =
      max (completion A P δo k) (completion A P δo j))
    (hjr : completion A P δr j ≤ completion A P δr k) :
    ∀ y : ℝ,
      (completion A P δr j ≤ (y : WithTop ℝ) ∧
          (y : WithTop ℝ) < min (completion A P δo k) (completion A P δo j) →
        numInSystem A P δr y + 1 = numInSystem A P δo y) ∧
      (¬ (completion A P δr j ≤ (y : WithTop ℝ) ∧
          (y : WithTop ℝ) < min (completion A P δo k) (completion A P δo j)) →
        numInSystem A P δr y = numInSystem A P δo y) := by sorry
end SchrageSRPT.Opt
