-- Prove2me | Theorems.Thm_RobustPoA_Static_chain_16_21
-- name    : RobustPoA.Static.chain_16_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:42:02.323647+00:00
-- url     : https://prove2.me/theorems/430f103b-a45d-431d-a831-cd10c26be90f
-- title:
--   Proof of Theorem 3.2, (16)–(21), p. 13 — in a (λ, µ)-smooth game with µ < 1, every coarse correlated equilibrium has E[C(s)] ≤ λ/(1 − µ)·C(s*)
-- statement:
--   Let $G$ be a cost-minimization game with players $i$, player costs $C_i$ and joint cost $C(s) = \sum_i C_i(s)$, and suppose $G$ is $(\lambda,\mu)$-smooth with $\mu < 1$. Then for every coarse correlated equilibrium $\sigma$ of $G$ and every outcome $s^*$,
--
--   $$\mathbf{E}_{s\sim\sigma}[C(s)] \le \frac{\lambda}{1-\mu} \cdot C(s^*).$$
--
--   This is the conclusion of the chain (16)–(21) in the proof of Theorem 3.2, for one fixed smoothness pair $(\lambda,\mu)$; taking the infimum over admissible pairs gives Theorem 3.2.
--
--   **Formalization Note** Distributions are finitely supported probability weights on outcomes (see the definition item). No sign condition on $\lambda$ and no nonnegativity of costs is needed.
-- source:
--   Roughgarden, Intrinsic Robustness of the Price of Anarchy, J. ACM 62(5) (2015), proof of Theorem 3.2, (16)–(21), p. 13

import Mathlib
import Definitions.Def_RobustPoA_Static_Game
import Definitions.Def_RobustPoA_Static_Smoothness
import Definitions.Def_RobustPoA_Static_Distribution

namespace RobustPoA.Static

theorem chain_16_21 {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    (C : ι → (∀ i, S i) → ℝ) (lam mu : ℝ)
    (hsmooth : IsSmooth C lam mu) (hmu : mu < 1)
    (σ : (∀ i, S i) →₀ ℝ) (hσ : IsCCE C σ) (sstar : ∀ i, S i) :
    expect σ (cost C) ≤ lam / (1 - mu) * cost C sstar := by sorry

end RobustPoA.Static
