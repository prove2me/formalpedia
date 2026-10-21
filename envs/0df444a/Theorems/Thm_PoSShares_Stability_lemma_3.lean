-- Prove2me | Theorems.Thm_PoSShares_Stability_lemma_3
-- name    : PoSShares.Stability.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:31:29.062746+00:00
-- url     : https://prove2.me/theorems/8db4f246-da90-4d14-b79c-c182e8aed160
-- title:
--   Lemma 3 — the recursion (A16) stays in $[0,1]$ and is nondecreasing
-- statement:
--   Let $\nu > 0$ and $\theta_n \ge 0$ for all $n \ge 1$. Define
--   $$\alpha_1 = \Big(\frac{\theta_1}{\nu + \theta_1}\Big)^2, \qquad \alpha_{n+1} = \alpha_n + \Big(\frac{\theta_{n+1}}{\nu + \sum_{k=1}^{n+1}\theta_k}\Big)^2 (1 - \alpha_n).$$
--   Then for all $n \ge 1$,
--   $$\alpha_n \in [0, 1] \quad \text{and} \quad \alpha_n \le \alpha_{n+1}.$$
--
--   Applied with $\nu = N_0$ and $\theta = R$, it shows that the variance sequence $a_t$ is bounded and has a limit.
-- source:
--   Roşu, Saleh, Evolution of Shares in a Proof-of-Stake Cryptocurrency, author's manuscript of July 30, 2020 (sha256 90d9c06b…2b35eb), pp. 20–21, Lemma 3, (A16)

import Mathlib
import Definitions.Def_PoSShares_Stability_Model
import Definitions.Def_PoSShares_Stability_VarianceSeq

open MeasureTheory ProbabilityTheory Filter Topology

namespace PoSShares.Stability

/-- **Lemma 3, (A16)**, pp. 20–21. Roşu, Saleh, *Evolution of Shares in a Proof-of-Stake Cryptocurrency*, author's manuscript of
July 30, 2020 (sha256 90d9c06b…2b35eb).

Let `ν > 0` and `θ_n ≥ 0` for all `n ∈ ℕ₊`. Define `α_1 = (θ_1/(ν + θ_1))^2` and
`α_{n+1} = α_n + (θ_{n+1}/(ν + Σ_{k=1}^{n+1} θ_k))^2 (1 − α_n)` (`alphaSeq`). Then for all
`n ∈ ℕ₊`, `α_n ∈ [0, 1]` and `α_n ≤ α_{n+1}`. -/
theorem lemma_3 (ν : ℝ) (θ : ℕ → ℝ) (hν : 0 < ν) (hθ : ∀ n : ℕ, 1 ≤ n → 0 ≤ θ n) :
    ∀ n : ℕ, 1 ≤ n →
      alphaSeq ν θ n ∈ Set.Icc (0 : ℝ) 1 ∧ alphaSeq ν θ n ≤ alphaSeq ν θ (n + 1) := by sorry

end PoSShares.Stability
