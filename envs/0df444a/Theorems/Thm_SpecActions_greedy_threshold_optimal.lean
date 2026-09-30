-- Prove2me | Theorems.Thm_SpecActions_greedy_threshold_optimal
-- name    : SpecActions.greedy_threshold_optimal
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-10T19:03:48.345361+00:00
-- url     : https://prove2.me/theorems/1865909d-0953-4543-ab73-29bc57064e83
-- title:
--   Theorem 3 / Corollary 5 — optimality of the greedy threshold breadth
-- statement:
--   Fix a continuation value $\Delta>0$ and a marginal cost $c>0$, and consider the per-window objective
--
--   $$f(m)=q(m)\,\Delta-c\,m,\qquad m\in\{0,\dots,k\},$$
--
--   with $q$ as above and confidences sorted in descending order. If $m$ is an index at which the greedy stopping rule fires — that is, $c\le\Delta\,\delta q(j)$ for every $j<m$ and $\Delta\,\delta q(j)\le c$ for every $j\ge m$ — then $m$ maximizes $f$ over $\{0,\dots,k\}$.
--
--   This is the structural content of the confidence-aware selection theorem: the dynamic program collapses to a one-dimensional trade-off, so at runtime the system sorts confidences and adds branches greedily while the incremental hit probability scaled by $\Delta$ exceeds $c$, in $O(k)$ per step.
-- source:
--   Ye, Ahuja, Liargkovas, Lu, Kaffes, Peng, "Speculative Actions: A Lossless Framework for Faster Agentic Systems", ICLR 2026, arXiv:2510.04371, https://arxiv.org/abs/2510.04371, Theorem 3 (p. 10) and Corollary 5 with proof, Appendix C.3 (pp. 21–23)

import Definitions.Def_SpecActions_model

import Definitions.Def_SpecActions_model

namespace SpecActions
theorem greedy_threshold_optimal (pv : ℕ → ℝ) (Δ c : ℝ) (k : ℕ)
    (hΔ : 0 < Δ) (hc : 0 < c)
    (hpv0 : ∀ j, 0 ≤ pv j) (hpv1 : ∀ j, pv j ≤ 1)
    (hsorted : ∀ i j, i ≤ j → pv j ≤ pv i)
    (m : ℕ) (hm : m ≤ k)
    (hbelow : ∀ j < m, c ≤ Δ * dqhit pv j)
    (habove : ∀ j, m ≤ j → Δ * dqhit pv j ≤ c) :
    ∀ n ≤ k, specObjective pv Δ c n ≤ specObjective pv Δ c m := by sorry
end SpecActions
