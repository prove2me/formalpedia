-- Prove2me | Theorems.Thm_VLearning_CCE_lemma_14
-- name    : VLearning.CCE.lemma_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:29:43.099181+00:00
-- url     : https://prove2.me/theorems/f5d5de6b-daff-41d0-b6c5-b94c0f53bf1a
-- title:
--   Lemma 14 (Pessimism), p. 22 — w.p. ≥ 1 − δ, V̲^k_{j,h}(s) ≤ V^{π̂^k_h}_{j,h}(s) for every (s, h, k, j)
-- statement:
--   There is a universal constant $c_0>0$ with the following property. Under the same hypotheses as Lemma 13 (standing assumptions, valid bandit rules satisfying Assumption 1 with $\xi$, nonnegative bonuses with $\sum_{i=1}^t\alpha^i_t\beta_{j,i}\ge c_0(H\xi(A_j,t,\iota)+\sqrt{H^3\iota/t})$ for $t\in[K]$, $\iota=\log(mHSAK/\delta)$), for any $\delta\in(0,1]$, with probability at least $1-\delta$ over the training run,
--   $$\underline V^k_{j,h}(s)\le V^{\hat\pi^k_h}_{j,h}(s)\qquad\text{for all }(s,h,k,j)\in\mathcal S\times[H]\times[K]\times[m],$$
--   where $\underline V$ is the pessimistic estimate (10)–(11) and the right side is player $j$'s value of the correlated output policy started at step $h$ with index $k$.
--
--   Pessimism makes $\underline V^k$ a lower bound on the output policy's own value, the second half of the gap bound.
--
--   **Formalization Note** Only the lower half of the $\Theta$ bonus condition is assumed, with its constant $c_0$ quantified before every instance. Bonuses are assumed nonnegative.
-- source:
--   Jin, Liu, Wang & Yu, V-Learning—A Simple, Efficient, Decentralized Algorithm for Multiagent RL, arXiv:2110.14555v1, p. 22, Lemma 14 (Pessimism), with (10)–(11)

import Mathlib
import Definitions.Def_VLearning_CCE_Model

namespace VLearning.CCE

/-- Lemma 14 (Pessimism, p. 22): for a bonus at least `c₀ (Hξ(A_j, t, ι) + √(H³ι/t))` (the lower half
of Theorem 6's `Θ`, with a universal `c₀`), for any `δ ∈ (0, 1]`, with probability at least `1 − δ`,
`V̲^k_{j,h}(s) ≤ V^{π̂^k_h}_{j,h}(s)` for every `(s, h, k, j)`. -/
theorem lemma_14 :
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
            (runState G β τ k.val).vLow j h s ≤ outVal G alg β τ j h.val k s) := by sorry

end VLearning.CCE
