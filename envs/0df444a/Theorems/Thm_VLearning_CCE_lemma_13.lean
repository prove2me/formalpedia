-- Prove2me | Theorems.Thm_VLearning_CCE_lemma_13
-- name    : VLearning.CCE.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:29:33.425628+00:00
-- url     : https://prove2.me/theorems/ef1db2a2-0b10-4a37-a109-ffa5cf429788
-- title:
--   Lemma 13 (Optimism), p. 20 — w.p. ≥ 1 − δ, V^k_{j,h}(s) ≥ V^{†,π̂^k_{−j,h}}_{j,h}(s) for every (s, h, k, j)
-- statement:
--   There is a universal constant $c_0>0$ with the following property. Consider $m$ players running V-learning for $K\ge1$ episodes on a Markov game satisfying the standing assumptions, each with a valid bandit rule satisfying Assumption 1 with the function $\xi$, and with nonnegative bonuses such that for every player $j$ and every $t\in[K]$
--   $$\sum_{i=1}^t\alpha^i_t\beta_{j,i}\ge c_0\Big(H\xi(A_j,t,\iota)+\sqrt{H^3\iota/t}\Big),\qquad \iota=\log(mHSAK/\delta).$$
--   Then for any $\delta\in(0,1]$, with probability at least $1-\delta$ over the training run,
--   $$V^k_{j,h}(s)\ge V^{\dagger,\hat\pi^k_{-j,h}}_{j,h}(s)\qquad\text{for all }(s,h,k,j)\in\mathcal S\times[H]\times[K]\times[m],$$
--   where the right side is the best value player $j$ can obtain from step $h$ against the other players' part of the output policy started at step $h$ with index $k$.
--
--   Optimism makes the maintained values $V^k$ upper bounds on every best-response value, the first half of the gap bound.
--
--   **Formalization Note** The lemma is stated under the conditions of Appendix B (Assumption 1 and the bonus condition of Theorem 6); only the lower half of the $\Theta$ bonus condition is needed, with its constant $c_0$ quantified before every instance. Bonuses are assumed nonnegative.
-- source:
--   Jin, Liu, Wang & Yu, V-Learning—A Simple, Efficient, Decentralized Algorithm for Multiagent RL, arXiv:2110.14555v1, p. 20, Lemma 13 (Optimism), under the conditions stated at the start of Appendix B

import Mathlib
import Definitions.Def_VLearning_CCE_Model

namespace VLearning.CCE

/-- Lemma 13 (Optimism, p. 20): for a bonus at least `c₀ (Hξ(A_j, t, ι) + √(H³ι/t))` (the lower half
of Theorem 6's `Θ`, with a universal `c₀`), for any `δ ∈ (0, 1]`, with probability at least `1 − δ`,
`V^k_{j,h}(s) ≥ V^{†, π̂^k_{−j,h}}_{j,h}(s)` for every `(s, h, k, j)`. -/
theorem lemma_13 :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (G : Game), G.Standing →
      ∀ (alg : ∀ j, BanditRule (G.A j)), (∀ j, (alg j).Valid) →
      ∀ (ξ : ℕ → ℕ → ℝ → ℝ), (∀ j, Assumption1 G.H (alg j) ξ) →
      ∀ (β : Fin G.m → ℕ → ℝ), (∀ j t, 0 ≤ β j t) →
      ∀ (δ : ℝ), 0 < δ → δ ≤ 1 → ∀ K : ℕ, 1 ≤ K →
        (∀ j t, 1 ≤ t → t ≤ K →
          c₀ * bonusScale G ξ (G.A j) (iota G K δ) t ≤
            ∑ i ∈ Finset.Icc 1 t, lrW G.H t i * β j i) →
        1 - δ ≤ trainProb G alg β K (fun τ =>
          ∀ (s : Fin G.S) (h : Fin G.H) (k : Fin K) (j : Fin G.m),
            brValFrom G alg β τ j h.val k s ≤ (runState G β τ k.val).vUp j h s) := by sorry

end VLearning.CCE
