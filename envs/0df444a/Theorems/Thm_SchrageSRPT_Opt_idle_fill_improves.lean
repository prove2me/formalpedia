-- Prove2me | Theorems.Thm_SchrageSRPT_Opt_idle_fill_improves
-- name    : SchrageSRPT.Opt.idle_fill_improves
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:22:26.734092+00:00
-- url     : https://prove2.me/theorems/2ded11ed-e57c-497a-900b-18fdf6a173fe
-- title:
--   PROOF, p. 689, case (b1) — processing an idle-waiting job j over an idle interval reduces C(j) and leaves every other C(i) unchanged
-- statement:
--   Let $\delta_o$ be a schedule of an arrival stream $\{A(n), P(n)\}$, let $t \in \mathbb R$ and $v > 0$, and let $j$ be a job in system at time $t$ under $\delta_o$. Suppose that over the interval $[t, t+v]$
--
--   1. job $j$ is not processed: $\delta_o(j, x) = 0$ for $t \le x \le t + v$;
--   2. the processor is idle with respect to the jobs in system (condition (b1)): $\delta_o(k, x) = 0$ for every $k \in \theta_o(x)$ and $t \le x \le t+v$;
--
--   and that $j$ completes under $\delta_o$, i.e. $C_o(j) < \infty$. Let $\delta_r$ be the revised schedule that processes $j$ throughout $[t, t+v]$ and agrees with $\delta_o$ elsewhere. Then
--   $$C_r(j) < C_o(j) \qquad\text{and}\qquad C_r(i) = C_o(i) \ \text{ for every } i \ne j.$$
--
--   This is the first case of the letter's interchange argument: a schedule that leaves the processor idle while a job is waiting can be improved.
--
--   **Formalization Note.** The letter's condition (a) also requires $S_o(j, x) < S_o(k, x)$ for the jobs $k$ in system; that clause is not needed in case (b1) and is omitted, which makes the statement stronger. The hypothesis $C_o(j) < \infty$ is added: if $j$ never completes under $\delta_o$ it need not complete under $\delta_r$ either, and "$C(j)$ can be reduced" has no content. The revised schedule switches every other job off on $[t, t+v]$ so that it is again a schedule; this only removes service from jobs that have already completed, so it does not change their completion times. That the revision is a schedule follows from the hypotheses and is not assumed.
-- source:
--   Schrage, A proof of the optimality of the shortest remaining processing time discipline, Oper. Res. 16 (1968), p. 689, PROOF, conditions (a), (b1) and the sentence after (b)

import Mathlib
import Definitions.Def_SchrageSRPT_Opt_Model

namespace SchrageSRPT.Opt
theorem idle_fill_improves (A P : ℕ → ℝ) (δo : ℕ → ℝ → ℝ) (hδo : IsSchedule A δo)
    (j : ℕ) (t v : ℝ) (hv : 0 < v) (hj : j ∈ inSystem A P δo t)
    (hj_idle : ∀ x ∈ Set.Icc t (t + v), δo j x = 0)
    (hb1 : ∀ x ∈ Set.Icc t (t + v), ∀ k ∈ inSystem A P δo x, δo k x = 0)
    (hCj : completion A P δo j ≠ ⊤) :
    completion A P (idleFill δo j t v) j < completion A P δo j ∧
      ∀ i, i ≠ j → completion A P (idleFill δo j t v) i = completion A P δo i := by sorry
end SchrageSRPT.Opt
