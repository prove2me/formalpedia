-- Prove2me | Theorems.Thm_RobustPoA_Static_theorem_4_1
-- name    : RobustPoA.Static.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:42:11.821172+00:00
-- url     : https://prove2.me/theorems/8e486cce-12cf-4a18-b381-a126a70b4cf2
-- title:
--   Theorem 4.1, p. 16 — every ε-coarse correlated equilibrium of a (λ, µ)-smooth game with ε < 1/µ − 1 has E[C(s)] ≤ (1 + ε)λ/(1 − µ(1 + ε))·C(s*)
-- statement:
--   **Theorem 4.1 (Extension Theorem for Approximate Equilibria).** Let $G$ be a $(\lambda,\mu)$-smooth cost-minimization game with players $i$, player costs $C_i$ and joint cost $C(s) = \sum_i C_i(s)$. Let $\epsilon \ge 0$ with $\mu(1+\epsilon) < 1$. Then for every $\epsilon$-coarse correlated equilibrium $\sigma$ of $G$ and every outcome $s^*$ of $G$,
--
--   $$\mathbf{E}_{s\sim\sigma}[C(s)] \le \frac{(1+\epsilon)\lambda}{1-\mu(1+\epsilon)} \cdot C(s^*). \tag{27}$$
--
--   The theorem shows that smoothness bounds degrade gracefully with the approximation parameter; at $\epsilon = 0$ it is the fixed-pair form of Theorem 3.2.
--
--   **Formalization Note** The paper's condition "$\epsilon < 1/\mu - 1$" is encoded as $\mu(1+\epsilon) < 1$: the two agree for $0 < \mu < 1$, the printed form is meaningless at $\mu = 0$ (in Lean $1/0 = 0$ would make it $\epsilon < -1$, a vacuous hypothesis) and reverses for $\mu < 0$. The condition $\epsilon \ge 0$ is the paper's implicit domain of an approximation parameter. The $\epsilon$-coarse correlated equilibrium is the extension of (15) that §4.1 describes as defined "in the same way" as (26). Distributions are finitely supported.
-- source:
--   Roughgarden, Intrinsic Robustness of the Price of Anarchy, J. ACM 62(5) (2015), Theorem 4.1 (27), p. 16

import Mathlib
import Definitions.Def_RobustPoA_Static_Game
import Definitions.Def_RobustPoA_Static_Smoothness
import Definitions.Def_RobustPoA_Static_Distribution

namespace RobustPoA.Static

theorem theorem_4_1 {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    (C : ι → (∀ i, S i) → ℝ) (lam mu ε : ℝ)
    (hsmooth : IsSmooth C lam mu) (hε : 0 ≤ ε) (hεmu : mu * (1 + ε) < 1)
    (σ : (∀ i, S i) →₀ ℝ) (hσ : IsEpsCCE C ε σ) (sstar : ∀ i, S i) :
    expect σ (cost C) ≤ (1 + ε) * lam / (1 - mu * (1 + ε)) * cost C sstar := by sorry

end RobustPoA.Static
