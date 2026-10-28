-- Prove2me | Theorems.Thm_ScheduledQueue_Stability_upper_decomposition
-- name    : ScheduledQueue.Stability.upper_decomposition
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:07:51.81927+00:00
-- url     : https://prove2.me/theorems/ad4f14d3-a4bb-451e-9d0b-2d2ea180b597
-- title:
--   Proof of Theorem 1, pp. 5–6 — upper decomposition #{j : R_j ∈ (0, s]} ≤ β₁(s) + ⌊s/h⌋ + 1 + β₂(s)
-- statement:
--   Let $h>0$, let $(\xi_j)_{j\in\mathbb Z}$ and $U$ be arbitrary real numbers (one outcome), and let $R_j=jh+Uh-\xi_j$ be the reversed arrival times. For every $s\ge0$,
--   $$\#\{j\in\mathbb Z : R_j\in(0,s]\}\;\le\;\beta_1(s)+\lfloor s/h\rfloor+1+\beta_2(s),$$
--   where $\beta_1(s)=\#\{j\ge1: R_{-j}\in(0,s]\}$ and $\beta_2(s)=\#\{j\ge\lfloor s/h\rfloor+1 : R_j\in(0,s]\}$. Multiplying by $h$,
--   $$\Lambda(s)-s\le h\big(\beta_1(s)+\beta_2(s)+1\big).$$
--
--   This is the inequality the proof of Theorem 1 uses to bound $M(t)$ from above by the two quantities $\beta_1$ (controlled by $\Gamma_1$) and $\beta_2$ (controlled by the upper bound on the perturbations).
--
--   **Formalization Note.** The page states an identity $\Lambda(s)-h\lfloor s/h\rfloor=\beta_1(s)+\beta_2(s)-\beta_3(s)-\beta_4(s)$ and then "$M(t)\le\max_s\beta_1(s)+\max_s\beta_2(s)$". As printed the identity omits the customer $j=0$, its $\beta_4$ sums over all $j\ge1$ (so it is infinite), and it mixes the units of $\Lambda$ (time) and of the counts. This statement is the corrected one-sided inequality, in counts valued in $\mathbb N\cup\{\infty\}$; it holds for every outcome and needs no assumption on $U$.
-- source:
--   Araman and Glynn, Stability of a Queue Fed by Scheduled Traffic at Critical Loading, arXiv:2212.04164v1, pp. 5–6, proof of Theorem 1, the display Λ(s) − h⌊s/h⌋ = β₁(s) + β₂(s) − β₃(s) − β₄(s) and "Of course, M(t) ≤ max β₁(s) + max β₂(s)" (corrected)

import Mathlib
import Definitions.Def_ScheduledQueue_Stability_Setting
import Definitions.Def_ScheduledQueue_Stability_Reversed

open MeasureTheory ProbabilityTheory Set Filter Topology ENNReal

namespace ScheduledQueue.Stability

theorem upper_decomposition {Ω : Type*} (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ)
    (U : Ω → ℝ) :
    ∀ (ω : Ω) (s : ℝ), 0 ≤ s →
      revCount h ξ U s ω ≤ beta1 h ξ U s ω + ((⌊s / h⌋₊ + 1 : ℕ) : ℕ∞) + beta2 h ξ U s ω := by sorry

end ScheduledQueue.Stability
