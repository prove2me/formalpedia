-- Prove2me | Theorems.Thm_RobustPoA_Static_eps_nash_bound
-- name    : RobustPoA.Static.eps_nash_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:41:34.700405+00:00
-- url     : https://prove2.me/theorems/f8e69c1c-269f-4472-a6b4-6f0433433cae
-- title:
--   §4.1, p. 16 — every ε-Nash equilibrium of a (λ, µ)-smooth game with ε < 1/µ − 1 costs at most (1 + ε)λ/(1 − µ(1 + ε)) times optimal
-- statement:
--   Let $G$ be a $(\lambda,\mu)$-smooth cost-minimization game with players $i$, player costs $C_i$ and joint cost $C(s) = \sum_i C_i(s)$. Let $\epsilon \ge 0$ with $\mu(1+\epsilon) < 1$, let $s$ be an $\epsilon$-Nash equilibrium of $G$, and let $s^*$ be an optimal outcome, i.e. $C(s^*) \le C(t)$ for every outcome $t$. Then
--
--   $$C(s) \le \frac{(1+\epsilon)\lambda}{1-\mu(1+\epsilon)} \cdot C(s^*).$$
--
--   This is the approximate-equilibrium version of the pure Nash bound; Theorem 4.1 extends it to $\epsilon$-coarse correlated equilibria.
--
--   **Formalization Note** The paper's condition "$\epsilon < 1/\mu - 1$" is encoded as $\mu(1+\epsilon) < 1$, which is what the derivation uses: the two agree for $0 < \mu < 1$, while for $\mu = 0$ the printed form is meaningless (and in Lean $1/0 = 0$ would make it $\epsilon < -1$) and for $\mu < 0$ it reverses. The condition $\epsilon \ge 0$ is the paper's implicit domain of an approximation parameter. Optimality of $s^*$ is kept as printed, although the bound holds for every outcome $s^*$.
-- source:
--   Roughgarden, Intrinsic Robustness of the Price of Anarchy, J. ACM 62(5) (2015), §4.1, first paragraph of p. 16 (with (26), p. 15)

import Mathlib
import Definitions.Def_RobustPoA_Static_Game
import Definitions.Def_RobustPoA_Static_Smoothness

namespace RobustPoA.Static

theorem eps_nash_bound {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    (C : ι → (∀ i, S i) → ℝ) (lam mu ε : ℝ)
    (hsmooth : IsSmooth C lam mu) (hε : 0 ≤ ε) (hεmu : mu * (1 + ε) < 1)
    (s : ∀ i, S i) (hs : IsEpsNash C ε s)
    (sstar : ∀ i, S i) (hopt : ∀ t : ∀ i, S i, cost C sstar ≤ cost C t) :
    cost C s ≤ (1 + ε) * lam / (1 - mu * (1 + ε)) * cost C sstar := by sorry

end RobustPoA.Static
