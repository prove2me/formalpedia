-- Prove2me | Theorems.Thm_QueueingFundamentals_GM1_arrival_point_means
-- name    : QueueingFundamentals.GM1.arrival_point_means
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T10:03:37.550319+00:00
-- url     : https://prove2.me/theorems/91112964-b729-4e8a-9a4f-6b1ef33bf0d5
-- title:
--   Eq. (5.61) — $L^{(A)} = r_0/(1-r_0)$ and $L_q^{(A)} = r_0^2/(1-r_0)$
-- statement:
--   Consider the G/M/1 queue with interarrival law $A$ on $[0,\infty)$ of mean $1/\lambda$ ($\lambda>0$), exponential service at rate $\mu>0$, and $\lambda/\mu < 1$. Let $r_0 \in (0,1)$ be the root of $z = \beta(z)$, and let $q = \{q_n\}$ be a stationary arrival-point probability vector ($qP = q$, $qe = 1$). Then the mean number in the system and the mean number in queue found by an arrival are
--   $$
--   L^{(A)} = \sum_{n\ge0} n q_n = \frac{r_0}{1 - r_0}, \qquad L_q^{(A)} = \sum_{n\ge1} (n-1) q_n = \frac{r_0^2}{1 - r_0}.
--   $$
--
--   The superscript $(A)$ records that these measures are taken at arrival points only.
--
--   **Formalization Note** $L_q^{(A)}$ is written $\sum_{n\ge0} n\, q_{n+1}$. Both series are asserted to converge.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.263, Eq. (5.61)

import Mathlib
import Definitions.Def_QueueingFundamentals_GM1_EmbeddedChain

namespace QueueingFundamentals.GM1

open MeasureTheory

/-- Eq. (5.61): at arrival points, the mean number in the system is `L^{(A)} = r_0/(1 - r_0)` and the
mean number in queue is `L_q^{(A)} = r_0^2/(1 - r_0)`. -/
theorem arrival_point_means (A : Measure ℝ) (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hA : IsInterarrivalLaw A lam) (hrho : lam / mu < 1)
    (r0 : ℝ) (hr0 : r0 ∈ Set.Ioo (0 : ℝ) 1) (hroot : beta A mu (r0 : ℂ) = (r0 : ℂ))
    (q : ℕ → ℝ) (hq : IsArrivalPointStationary A mu q) :
    HasSum (fun n : ℕ => (n : ℝ) * q n) (r0 / (1 - r0)) ∧
      HasSum (fun n : ℕ => (n : ℝ) * q (n + 1)) (r0 ^ 2 / (1 - r0)) := by sorry

end QueueingFundamentals.GM1
