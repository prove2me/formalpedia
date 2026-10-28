-- Prove2me | Theorems.Thm_PeriodicMAB_Lower_lemma_12
-- name    : PeriodicMAB.Lower.lemma_12
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:07:22.368948+00:00
-- url     : https://prove2.me/theorems/937ed18c-fbda-497f-b2f9-41478f01a9fc
-- title:
--   Lemma 12, p. 23 — stationary Gaussian bandits: every policy has regret ≥ √T/(8√2e) on some instance
-- statement:
--   Let $K \ge 2$ and let $T \ge 0$ be the horizon. Consider unit-variance Gaussian $K$-armed bandits whose arms are stationary: arm $k$ pays rewards drawn from $\mathcal N(\mu_k, 1)$, and every arm other than the first has the known mean $\mu_k = 1/2$, while the first arm's mean $\mu_1 \in [0,1]$ is unknown. For every policy $\pi$ there is a value $\mu_1 \in [0,1]$ such that the expected regret of $\pi$ on this instance satisfies
--   $$\mathbb E_\nu[R^\pi_T] \ge \frac{1}{8\sqrt2\, e}\sqrt T.$$
--
--   In particular $\sup_{\nu \in \mathcal E_1} \mathbb E_\nu[R^\pi_T] \ge \sqrt T/(8\sqrt 2 e)$, which is the printed form of Lemma 12. It is the base case of the lower bounds of §5: Lemma 13 applies it to each phase of a periodic arm.
--
--   **Formalization Note** The regret is the platform's `BanditAlgorithm.banditRegret`, $T\mu^* - \mathbb E[\sum_{t} X_t]$; for Gaussian arms it equals the paper's (1). "A policy that knows $\mu_k$ for $k \ge 2$" is formalized by fixing $\mu_k = 1/2$ for the arms other than the first (index $0$), the values the proof uses: with arbitrary known values the printed statement would fail (if the second arm is known to have mean $1$, pulling it always has regret $0$). The hypothesis $K \ge 2$ is added: with one arm the regret is $0$. No lower bound on $T$ is assumed.
-- source:
--   Chen, Wang and Wang, Learning and Optimization with Seasonal Patterns, arXiv:2005.08088v4, p. 23, Lemma 12 (proof pp. 46–47, (B-45))

import Mathlib
import Definitions.Def_BanditPolicy
import Definitions.Def_GaussianBandit
import Definitions.Def_banditRegret

namespace PeriodicMAB.Lower

open BanditAlgorithm

theorem lemma_12 (K T : ℕ) [NeZero K] (hK : 2 ≤ K) (π : BanditPolicy K) :
    ∃ μ₁ ∈ Set.Icc (0 : ℝ) 1,
      Real.sqrt T / (8 * Real.sqrt 2 * Real.exp 1) ≤
        banditRegret (gaussianBandit (Function.update (fun _ ↦ (1 / 2 : ℝ)) 0 μ₁)) π T := by sorry

end PeriodicMAB.Lower
