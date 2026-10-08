-- Prove2me | Theorems.Thm_SchrageSRPT_Opt_srpt_reassign_min_lt
-- name    : SchrageSRPT.Opt.srpt_reassign_min_lt
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:22:31.947338+00:00
-- url     : https://prove2.me/theorems/879ecba0-636d-429e-bf5d-675a6e34855f
-- title:
--   PROOF, p. 689, relation (2) — in case (b2) the SRPT reassignment strictly reduces min[C(k), C(j)]
-- statement:
--   Let $\delta_o$ be a schedule of an arrival stream, let $t \in \mathbb R$, $v > 0$, and let $j \ne k$ be two jobs in system at time $t$ under $\delta_o$ such that
--
--   1. job $k$ is processed throughout $[t, t+v]$: $\delta_o(k, x) = 1$ for $t \le x \le t+v$ (condition (b2));
--   2. $j$ has the shorter remaining time at $t$: $S_o(j, t) < S_o(k, t)$ (condition (a));
--   3. at least one of $j, k$ completes under $\delta_o$: $\min[C_o(k), C_o(j)] < \infty$.
--
--   Let $\delta_r$ be the SRPT reassignment of the pair after time $t$ (from $t$ on, the pair's capacity goes to $j$ until $j$ has received $S_o(j, t)$, then to $k$). Then
--   $$\min[C_r(k), C_r(j)] < \min[C_o(k), C_o(j)].$$
--
--   This is relation (2) of the letter's PROOF: when the processor serves a job with longer remaining time while a shorter one waits, swapping their service makes the first of the two completions strictly earlier.
--
--   **Formalization Note.** Condition (a) of the letter requires $S_o(j, x) < S_o(k, x)$ for all $x \in [t, t+v]$; only $x = t$ is used, which makes the statement stronger. Hypothesis 3 is added: if neither job completes under $\delta_o$, both minima can be $+\infty$ and the strict inequality fails. That $\delta_r$ is a schedule follows from the hypotheses and is not assumed. Completion times take values in $\mathbb R \cup \{+\infty\}$.
-- source:
--   Schrage, A proof of the optimality of the shortest remaining processing time discipline, Oper. Res. 16 (1968), p. 689, PROOF, conditions (a), (b2) and the display "min[C_r(k), C_r(j)] < min[C_o(k), C_o(j)]" (relation (2))

import Mathlib
import Definitions.Def_SchrageSRPT_Opt_Model

namespace SchrageSRPT.Opt
theorem srpt_reassign_min_lt (A P : ℕ → ℝ) (δo : ℕ → ℝ → ℝ) (hδo : IsSchedule A δo)
    (j k : ℕ) (t v : ℝ) (hv : 0 < v) (hjk : j ≠ k)
    (hj : j ∈ inSystem A P δo t) (hk : k ∈ inSystem A P δo t)
    (hk_served : ∀ x ∈ Set.Icc t (t + v), δo k x = 1)
    (hS : remaining A P δo j t < remaining A P δo k t)
    (hfinite : min (completion A P δo k) (completion A P δo j) ≠ ⊤) :
    min (completion A P (srptReassign A P δo j k t) k)
        (completion A P (srptReassign A P δo j k t) j) <
      min (completion A P δo k) (completion A P δo j) := by sorry
end SchrageSRPT.Opt
