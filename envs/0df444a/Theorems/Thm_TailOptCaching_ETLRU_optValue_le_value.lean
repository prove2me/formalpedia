-- Prove2me | Theorems.Thm_TailOptCaching_ETLRU_optValue_le_value
-- name    : TailOptCaching.ETLRU.optValue_le_value
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:23:28.918495+00:00
-- url     : https://prove2.me/theorems/b51ea97a-2e80-4301-98b1-d6aea91d305e
-- title:
--   App. B, p. 17 — the finite-horizon Bellman optimum lower-bounds the expected total TEL of every admissible policy
-- statement:
--   Let $V^\star_M$ be the finite-horizon value-to-go function of App. B: $V^\star_0 = 0$ and, from a post-decision state $z$,
--   $$V^\star_{M+1}(z) = \mathbb E_{d}\,\mathbb E_{\theta, Q, A}\Big[(L_\theta + Q - X_\theta - \xi)^+ + \min_{Y \in \mathcal X(X, \theta, L_\theta + Q + A)} V^\star_M\big(\Gamma\Psi(\Phi_d z), Y\big)\Big],$$
--   where $\Phi_d$ multiplies all belief rates by the decay factor $d$, $(\theta, Q, A)$ is the next arrival, and $\mathcal X$ is the feasible set given by (9), (10) and the capacity constraint. For every policy $\pi$ whose decisions are always feasible, every horizon $M$, every starting stage $k$ and every state $z$,
--   $$V^\star_M(z) \le V^\pi_M(z),$$
--   where $V^\pi_M(z)$ is the expected total TEL of the next $M$ arrivals under $\pi$.
--
--   This is the half of the dynamic-programming principle that makes the Bellman recursion a benchmark: any policy attaining $V^\star$ is optimal.
--
--   **Formalization Note.** The minimum over $\mathcal X$ is an infimum in $[0, \infty]$; no well-formedness of $z$ is needed.
-- source:
--   Zhang, Li, Moallemi & Peng, Tail-Optimized Caching for LLM Inference, arXiv:2510.15152v1, p. 17, App. B (finite-horizon value-to-go function)

import Mathlib
import Definitions.Def_TailOptCaching_ETLRU_Model

open scoped ENNReal

namespace TailOptCaching.ETLRU

theorem optValue_le_value (P : Params) (π : Policy) (hπ : Admissible P π) (M k : ℕ)
    (z : State) :
    optValue P M z ≤ value P π M k z := by sorry

end TailOptCaching.ETLRU
