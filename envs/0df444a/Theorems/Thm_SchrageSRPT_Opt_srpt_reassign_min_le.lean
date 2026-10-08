-- Prove2me | Theorems.Thm_SchrageSRPT_Opt_srpt_reassign_min_le
-- name    : SchrageSRPT.Opt.srpt_reassign_min_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:22:33.782884+00:00
-- url     : https://prove2.me/theorems/7ae20f13-a9ba-4024-9064-25cc8a4a3556
-- title:
--   PROOF, p. 689 — scheduling j and k by SRPT over σ minimizes min[C(k), C(j)]
-- statement:
--   Let $\delta_o$ be a schedule of an arrival stream, let $t \in \mathbb R$, and let $j \ne k$ be two jobs in system at time $t$ under $\delta_o$ with
--   $$S_o(j, t) < S_o(k, t).$$
--   Let $\delta_s$ be the SRPT reassignment of the pair after time $t$: from time $t$ on, the capacity $\delta_o(j, x) + \delta_o(k, x)$ goes to $j$ until $j$ has received $S_o(j, t)$, and to $k$ afterwards. Let $\delta_r$ be any schedule of the same stream that agrees with $\delta_o$ on $j$ and $k$ before $t$ and gives the pair the same capacity, $\delta_r(j, x) + \delta_r(k, x) = \delta_o(j, x) + \delta_o(k, x)$ for all $x$. Then
--   $$\min[C_s(k), C_s(j)] \le \min[C_r(k), C_r(j)].$$
--
--   This is the letter's claim that "$\min[C(k), C(j)]$ is minimized if we schedule $k$ and $j$ according to SRPT", i.e. that the earliest time at which one of the two jobs can finish is attained by giving all the capacity to the job with the shorter remaining time.
--
--   **Formalization Note.** Completion times take values in $\mathbb R \cup \{+\infty\}$. That $\delta_s$ is a schedule follows from the hypotheses and is not assumed. The competitor $\delta_r$ may spend capacity on a completed job; that only delays its completions, so no restriction is placed on it. Other jobs play no role and are not constrained.
-- source:
--   Schrage, A proof of the optimality of the shortest remaining processing time discipline, Oper. Res. 16 (1968), p. 689, PROOF, the paragraph after the max identity

import Mathlib
import Definitions.Def_SchrageSRPT_Opt_Model

namespace SchrageSRPT.Opt
theorem srpt_reassign_min_le (A P : ℕ → ℝ) (δo δr : ℕ → ℝ → ℝ)
    (hδo : IsSchedule A δo) (hδr : IsSchedule A δr) (j k : ℕ) (t : ℝ) (hjk : j ≠ k)
    (hj : j ∈ inSystem A P δo t) (hk : k ∈ inSystem A P δo t)
    (hbefore : ∀ x, x < t → δr j x = δo j x ∧ δr k x = δo k x)
    (hsum : ∀ x, δr j x + δr k x = δo j x + δo k x)
    (hS : remaining A P δo j t < remaining A P δo k t) :
    min (completion A P (srptReassign A P δo j k t) k)
        (completion A P (srptReassign A P δo j k t) j) ≤
      min (completion A P δr k) (completion A P δr j) := by sorry
end SchrageSRPT.Opt
