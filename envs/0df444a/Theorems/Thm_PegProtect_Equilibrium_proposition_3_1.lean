-- Prove2me | Theorems.Thm_PegProtect_Equilibrium_proposition_3_1
-- name    : PegProtect.Equilibrium.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:33:21.442765+00:00
-- url     : https://prove2.me/theorems/c5b6eb79-ad11-4ee9-9e7c-022f89a3775b
-- title:
--   Proposition 3.1, p. 15 — the order imbalance has the unique steady state q_k = ((1−ω)/(1+ω)) ω^|k| (discrete Laplace)
-- statement:
--   Let $\omega\in(0,1)$ be the probability that an investor arrival is a midpoint peg order, and let $T$ be the operator of (A.1a)–(A.1c) describing how one arrival transforms the distribution of the order imbalance $k\in\mathbb Z$. Then the discrete Laplace law
--   $$q_k=\frac{1-\omega}{1+\omega}\,\omega^{|k|},\qquad k\in\mathbb Z,$$
--   is a probability distribution on $\mathbb Z$ with $Tq=q$, and it is the only one: every family $p=(p_k)_{k\in\mathbb Z}$ with $p_k\ge0$, $\sum_k p_k=1$ and $Tp=p$ equals $q$.
--
--   This is the steady state of the hidden midpoint queue; all expected surpluses of investors and the profit of market makers are computed under it.
--
--   **Formalization Note** A steady state is a fixed point of $T$ in the set of distributions on $\mathbb Z$ (Appendix A, p. 34). Summation over $\mathbb Z$ is unconditional (`HasSum`), which for nonnegative families is ordinary convergence.
-- source:
--   Aldrich & Friedman, Order Protection through Delayed Messaging, SSRN 2999059 (version of March 3, 2019), p. 15, Proposition 3.1, (3.1); restated p. 34 with proof pp. 34–35, operator (A.1a)–(A.1c) p. 34

import Mathlib
import Definitions.Def_PegProtect_Equilibrium_Model

namespace PegProtect.Equilibrium

theorem proposition_3_1 (ω : ℝ) (h0 : 0 < ω) (h1 : ω < 1) :
    IsDistribution (q ω) ∧ T ω (q ω) = q ω ∧
    ∀ p : ℤ → ℝ, IsDistribution p → T ω p = p → p = q ω := by sorry

end PegProtect.Equilibrium
