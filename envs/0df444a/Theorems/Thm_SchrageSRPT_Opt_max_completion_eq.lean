-- Prove2me | Theorems.Thm_SchrageSRPT_Opt_max_completion_eq
-- name    : SchrageSRPT.Opt.max_completion_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:22:31.742254+00:00
-- url     : https://prove2.me/theorems/a5e48ddc-a745-4892-97b4-0f8b497040b7
-- title:
--   PROOF, p. 689 — reassigning jobs j and k over σ leaves max{C(k), C(j)} unchanged
-- statement:
--   Let $\delta_o$ and $\delta_r$ be two schedules of the same arrival stream, let $t \in \mathbb R$, and let $j \ne k$ be two jobs in system at time $t$ under $\delta_o$. Suppose that
--
--   1. $\delta_r$ agrees with $\delta_o$ on $j$ and on $k$ before time $t$;
--   2. $\delta_r$ gives the pair the same capacity as $\delta_o$: $\delta_r(j, x) + \delta_r(k, x) = \delta_o(j, x) + \delta_o(k, x)$ for all $x$;
--   3. neither schedule processes $j$ or $k$ once that job has no remaining processing time: $S(i, x) \le 0$ implies $\delta(i, x) = 0$ for $i \in \{j, k\}$ and $\delta \in \{\delta_o, \delta_r\}$.
--
--   Then the later of the two completion times is the same under both schedules:
--   $$\max\{C_o(k), C_o(j)\} = \max\{C_r(k), C_r(j)\}.$$
--
--   In the letter's words, "regardless of how $j$ and $k$ are scheduled over $\sigma$, the last job will always finish at the same time". It is relation (3) of the letter's PROOF.
--
--   **Formalization Note.** The statement holds for every reassignment of the pair's capacity, not only the SRPT one, as the letter says. Hypothesis 3 is added: the letter's identity $\max\{C(k), C(j)\} = \min\{x : \int_t^x [\delta(k,y)+\delta(j,y)]\,dy \ge S(k,t)+S(j,t)\}$ fails if a schedule spends capacity on a job that has already completed. The letter does not require other jobs to be unchanged for this identity, and neither does the statement. Completion times take values in $\mathbb R \cup \{+\infty\}$.
-- source:
--   Schrage, A proof of the optimality of the shortest remaining processing time discipline, Oper. Res. 16 (1968), p. 689, PROOF, the displayed identity for max{C_o(k), C_o(j)} and relation (3)

import Mathlib
import Definitions.Def_SchrageSRPT_Opt_Model

namespace SchrageSRPT.Opt
theorem max_completion_eq (A P : ℕ → ℝ) (δo δr : ℕ → ℝ → ℝ)
    (hδo : IsSchedule A δo) (hδr : IsSchedule A δr) (j k : ℕ) (t : ℝ) (hjk : j ≠ k)
    (hj : j ∈ inSystem A P δo t) (hk : k ∈ inSystem A P δo t)
    (hbefore : ∀ x, x < t → δr j x = δo j x ∧ δr k x = δo k x)
    (hsum : ∀ x, δr j x + δr k x = δo j x + δo k x)
    (hwaste_o : ∀ i, (i = j ∨ i = k) → ∀ x, remaining A P δo i x ≤ 0 → δo i x = 0)
    (hwaste_r : ∀ i, (i = j ∨ i = k) → ∀ x, remaining A P δr i x ≤ 0 → δr i x = 0) :
    max (completion A P δo k) (completion A P δo j) =
      max (completion A P δr k) (completion A P δr j) := by sorry
end SchrageSRPT.Opt
