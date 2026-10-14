-- Prove2me | Theorems.Thm_ScheduledQueue_Stability_beta2_bounded
-- name    : ScheduledQueue.Stability.beta2_bounded
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:07:44.767989+00:00
-- url     : https://prove2.me/theorems/018ccaf8-5243-443c-901b-016087f5b818
-- title:
--   Proof of Theorem 1, p. 6 — if every ξ_j ≤ c, then β₂(s) ≤ ⌊c/h⌋ + 1
-- statement:
--   Fix one outcome of the scheduled-traffic model with $h>0$ and $U\in[0,1]$, and let $c\ge0$ be such that $\xi_j\le c$ for every $j\in\mathbb Z$. Then for every $s\ge0$,
--   $$\beta_2(s)=\#\{j\ge\lfloor s/h\rfloor+1 : jh+Uh-\xi_j\in(0,s]\}\;\le\;\Big\lfloor\frac ch\Big\rfloor+1 .$$
--
--   When the perturbations are bounded above, the number of customers scheduled after $s$ that arrive (in reversed time) before $s$ is bounded uniformly in $s$. Together with $\beta_1\le\Gamma_1$ this gives $M(\infty)<\infty$, the "if" half of Theorem 1.
--
--   **Formalization Note.** The page prints the bound $(\lfloor c\rfloor+1)/h$, which is false: with $h=2$, $c=1/2$ and $s$ just below $2$, the customer $j=1$ can satisfy $R_1\in(0,s]$, so $\beta_2(s)=1>1/2$. The page's middle step $I(\xi_{k(s)+j}\ge jh)$ should read $I(\xi_{k(s)+j}>(j-1)h)$, and the bound it gives is $\lfloor c/h\rfloor+1$, which is stated here. The statement is deterministic: "$\xi_0^+\le c$ a.s." is used through the full-measure event on which every $\xi_j\le c$. The count is valued in $\mathbb N\cup\{\infty\}$.
-- source:
--   Araman and Glynn, Stability of a Queue Fed by Scheduled Traffic at Critical Loading, arXiv:2212.04164v1, p. 6, proof of Theorem 1, display "β₂(s) ≤ … ≤ (⌊c⌋ + 1)/h" (constant corrected to ⌊c/h⌋ + 1)

import Mathlib
import Definitions.Def_ScheduledQueue_Stability_Setting
import Definitions.Def_ScheduledQueue_Stability_Reversed

open MeasureTheory ProbabilityTheory Set Filter Topology ENNReal

namespace ScheduledQueue.Stability

theorem beta2_bounded {Ω : Type*} (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ) :
    ∀ (ω : Ω) (c : ℝ), 0 ≤ c → (∀ j, ξ j ω ≤ c) → U ω ∈ Icc (0 : ℝ) 1 →
      ∀ s : ℝ, 0 ≤ s → beta2 h ξ U s ω ≤ ((⌊c / h⌋₊ + 1 : ℕ) : ℕ∞) := by sorry

end ScheduledQueue.Stability
