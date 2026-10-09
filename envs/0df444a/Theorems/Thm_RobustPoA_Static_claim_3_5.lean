-- Prove2me | Theorems.Thm_RobustPoA_Static_claim_3_5
-- name    : RobustPoA.Static.claim_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:41:37.582888+00:00
-- url     : https://prove2.me/theorems/9f572313-b9b1-4b34-ad1c-b8a1e8cb6c9f
-- title:
--   Claim (3)–(5), §2.1, p. 5 — in a (λ, µ)-smooth game with λ > 0, µ < 1, every pure Nash equilibrium costs at most λ/(1 − µ) times optimal
-- statement:
--   Let $G$ be a cost-minimization game with players $i$, player costs $C_i$ and joint cost $C(s) = \sum_i C_i(s)$. Suppose $G$ is $(\lambda,\mu)$-smooth with $\lambda > 0$ and $\mu < 1$, let $s$ be a pure Nash equilibrium of $G$, and let $s^*$ be an optimal outcome, i.e. $C(s^*) \le C(t)$ for every outcome $t$. Then
--
--   $$C(s) \le \frac{\lambda}{1-\mu} \cdot C(s^*).$$
--
--   This is the basic smoothness bound on the price of anarchy of pure Nash equilibria; the mission's extension theorems generalize it to coarse correlated and approximate equilibria.
--
--   **Formalization Note** The hypotheses $\lambda > 0$ and optimality of $s^*$ are kept exactly as the paper states the claim, although the inequality holds without them.
-- source:
--   Roughgarden, Intrinsic Robustness of the Price of Anarchy, J. ACM 62(5) (2015), claim (3)–(5), §2.1, p. 5

import Mathlib
import Definitions.Def_RobustPoA_Static_Game
import Definitions.Def_RobustPoA_Static_Smoothness

namespace RobustPoA.Static

theorem claim_3_5 {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    (C : ι → (∀ i, S i) → ℝ) (lam mu : ℝ)
    (hsmooth : IsSmooth C lam mu) (hlam : 0 < lam) (hmu : mu < 1)
    (s : ∀ i, S i) (hs : IsPureNash C s)
    (sstar : ∀ i, S i) (hopt : ∀ t : ∀ i, S i, cost C sstar ≤ cost C t) :
    cost C s ≤ lam / (1 - mu) * cost C sstar := by sorry

end RobustPoA.Static
