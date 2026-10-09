-- Prove2me | Theorems.Thm_RobustPoA_Static_theorem_3_2
-- name    : RobustPoA.Static.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:43:15.682632+00:00
-- url     : https://prove2.me/theorems/19652b9c-9f32-4e10-bab1-1ef29e259e58
-- title:
--   Theorem 3.2, p. 13 — every coarse correlated equilibrium σ of a game with robust POA ρ(G) satisfies E_{s∼σ}[C(s)] ≤ ρ(G)·C(s*)
-- statement:
--   **Theorem 3.2 (Extension Theorem — Static Version).** Let $G$ be a cost-minimization game with players $i$, player costs $C_i$, nonnegative joint cost $C(s) = \sum_i C_i(s) \ge 0$, and robust price of anarchy
--
--   $$\rho(G) = \inf\left\{ \tfrac{\lambda}{1-\mu} : \mu < 1,\ G \text{ is } (\lambda,\mu)\text{-smooth} \right\},$$
--
--   and suppose $G$ is $(\lambda,\mu)$-smooth for at least one pair with $\mu < 1$. Then for every coarse correlated equilibrium $\sigma$ of $G$ and every outcome $s^*$ of $G$,
--
--   $$\mathbf{E}_{s\sim\sigma}[C(s)] \le \rho(G) \cdot C(s^*).$$
--
--   Every price-of-anarchy bound proved by a smoothness argument therefore holds automatically for coarse correlated equilibria, and hence for mixed Nash and correlated equilibria as well as pure ones.
--
--   **Formalization Note** Two hypotheses are made explicit. (1) The joint cost is nonnegative: this is the paper's standing assumption of a nonnegative objective function (§1, p. 2; §2.4, p. 10); without it a negative $C(s^*)$ would reverse the passage to the infimum. Individual costs $C_i$ may be negative. (2) Some smoothness pair with $\mu < 1$ exists, i.e. $\rho(G) < +\infty$: on the page the statement is vacuous when $\rho(G) = +\infty$. In Lean $\rho(G)$ is an extended-real infimum (`EReal`), equal to $+\infty$ on the empty set, and the expected cost is compared in `EReal`; since `EReal` sets $(+\infty)\cdot 0 = 0$, the case $\rho(G) = +\infty$, $C(s^*) = 0$ would otherwise claim $\mathbf{E}[C] \le 0$. Distributions are finitely supported probability weights on outcomes, so distributions with infinite support are not covered.
-- source:
--   Roughgarden, Intrinsic Robustness of the Price of Anarchy, J. ACM 62(5) (2015), Theorem 3.2, p. 13

import Mathlib
import Definitions.Def_RobustPoA_Static_Game
import Definitions.Def_RobustPoA_Static_Smoothness
import Definitions.Def_RobustPoA_Static_Distribution

namespace RobustPoA.Static

theorem theorem_3_2 {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    (C : ι → (∀ i, S i) → ℝ)
    (hC : ∀ s, 0 ≤ cost C s)
    (hsmooth : ∃ lam mu : ℝ, mu < 1 ∧ IsSmooth C lam mu)
    (σ : (∀ i, S i) →₀ ℝ) (hσ : IsCCE C σ) (sstar : ∀ i, S i) :
    expect σ (cost C) ≤ robustPoA C * cost C sstar := by sorry

end RobustPoA.Static
