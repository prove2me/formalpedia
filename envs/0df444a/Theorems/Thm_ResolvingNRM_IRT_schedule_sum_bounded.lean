-- Prove2me | Theorems.Thm_ResolvingNRM_IRT_schedule_sum_bounded
-- name    : ResolvingNRM.IRT.schedule_sum_bounded
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T02:21:38.013829+00:00
-- url     : https://prove2.me/theorems/37c73513-775c-440c-bab7-47f975318d14
-- title:
--   p. 30 — the right-hand side of (13) at $K = K(T)$ is bounded uniformly in $T$
-- statement:
--   Let $K(T) = \lceil \log\log T / \log(6/5) \rceil$. For every $\kappa > 0$ there is a constant $B$ such that for every real $T \ge 1$,
--   $$\sum_{u=0}^{K(T)-1} T^{(5/6)^u}\exp\big(-\kappa\,T^{(5/6)^u/6}\big) + T^{(5/6)^{K(T)}/2} \le B .$$
--
--   This is the analytic half of the proof of Theorem 1: it shows that both terms of the regret decomposition (13), evaluated at the IRT schedule, are $O(1)$.
--
--   **Formalization Note** Only the bound is stated, not the chain of inequalities printed on p. 30; its second inequality replaces $x = T^{(5/6)^{K-\ell}}$ by the upper bound $e^{(6/5)^\ell}$ inside $x e^{-\kappa x^{1/6}}$, a function that is not increasing for $x > (6/\kappa)^6$. The bound itself holds because $T^{(5/6)^{K-\ell}} \ge e^{(6/5)^{\ell-1}}$ grows doubly exponentially in $\ell$. The convention for $K(T)$ at $1 \le T \le e$ is that of the definition file ($K = 0$).
-- source:
--   Bumpensanti, Wang, A Re-solving Heuristic with Uniformly Bounded Loss for Network Revenue Management, arXiv:1802.06192v3, Appendix B.1, p. 30 (bound on the right-hand side of (13))

import Mathlib
import Definitions.Def_RLPBidPrice_Unbiased_Model
import Definitions.Def_ResolvingNRM_IRT_Model

open RLPBidPrice.Unbiased Matrix

namespace ResolvingNRM.IRT

theorem schedule_sum_bounded (κ : ℝ) (hκ : 0 < κ) :
    ∃ B : ℝ, ∀ T : ℝ, 1 ≤ T →
      (∑ u ∈ Finset.range (Kirt T),
          T ^ ((5 / 6 : ℝ) ^ u) * Real.exp (-κ * T ^ ((5 / 6 : ℝ) ^ u / 6))) +
        T ^ ((5 / 6 : ℝ) ^ Kirt T / 2) ≤ B := by sorry

end ResolvingNRM.IRT
