-- Prove2me | Theorems.Thm_VLearning_CCE_theorem_6
-- name    : VLearning.CCE.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:29:50.40898+00:00
-- url     : https://prove2.me/theorems/faa2f7e7-ac9d-40fd-b31c-5dfc56e77eac
-- title:
--   Theorem 6, p. 11 — under Assumption 1 and a Θ(Hξ + √(H³ι/t)) bonus, w.p. ≥ 1 − δ the V-learning output policy is an O((H²S/K)Ξ(A,K/S,ι) + √(H⁵Sι/K))-CCE
-- statement:
--   Consider an $m$-player tabular episodic Markov game with $S$ states, episode length $H$, $A_j$ actions for player $j$ and rewards in $[0,1]$; let $A=\max_jA_j$. Every player runs V-learning (Algorithm 1) independently, with the learning rate $\alpha_t=(H+1)/(H+t)$ of (3) and an adversarial bandit subroutine satisfying Assumption 1 with a function $\xi(B,t,x)$ that is non-decreasing in $B$, together with an upper bound $\Xi(B,t,x)\ge\sum_{t'=1}^t\xi(B,t',x)$ concave in $t$.
--
--   For $\delta\in(0,1)$ and $K\ge1$ let $\iota=\log(mHSAK/\delta)$, and choose nonnegative bonuses with
--   $$\sum_{i=1}^t\alpha^i_t\beta_{j,i}=\Theta\Big(H\xi(A_j,t,\iota)+\sqrt{H^3\iota/t}\Big)\qquad\text{for every }t\in[K].$$
--   Then, with probability at least $1-\delta$ over the $K$ training episodes, the correlated output policy $\hat\pi=\hat\pi_1\odot\cdots\odot\hat\pi_m$ of Algorithm 3 (with a shared random seed) satisfies
--   $$\max_{j\in[m]}\Big[V^{\dagger,\hat\pi_{-j}}_{j,1}(s_1)-V^{\hat\pi}_{j,1}(s_1)\Big]\le O\Big(\frac{H^2S}{K}\,\Xi(A,K/S,\iota)+\sqrt{\frac{H^5S\iota}{K}}\Big),$$
--   that is, $\hat\pi$ is an approximate coarse correlated equilibrium.
--
--   The bound depends on the action sets only through $A=\max_jA_j$, not through $\prod_jA_j$: decentralized learning finds a CCE without the exponential dependence on the number of players.
--
--   **Formalization Note** $\Theta$ is read as: a universal lower constant $c_0$ (quantified before everything) and an arbitrary upper constant $c_1$; the $O$-constant $C$ depends on $c_1$ only. Each player may use its own bandit rule, all satisfying Assumption 1 with the same $\xi$. Bonuses are assumed nonnegative; $K\ge1$. The best response sees the full history of states and joint actions but not the output policy's latent episode index, so the supremum is taken outside the average over the uniform initial index.
-- source:
--   Jin, Liu, Wang & Yu, V-Learning—A Simple, Efficient, Decentralized Algorithm for Multiagent RL, arXiv:2110.14555v1, p. 11, Theorem 6 (first sentence); §5.1, p. 10; Definition 2, p. 6

import Mathlib
import Definitions.Def_VLearning_CCE_Model

namespace VLearning.CCE

/-- Theorem 6 (p. 11), first sentence. Suppose every player's `ADV_BANDIT_UPDATE` satisfies
Assumption 1 (with `ξ` non-decreasing in `B` and an upper bound `Ξ` concave in `t`). For any
`δ ∈ (0, 1)` and `K ≥ 1`, let `ι = log(mHSAK/δ)`, use the learning rate (3) and a bonus with
`∑_{i=1}^t α^i_t β_{j,i} = Θ(Hξ(A_j, t, ι) + √(H³ι/t))` for `t ∈ [K]` (lower constant `c₀`, upper
constant `c₁`). Then with probability at least `1 − δ` over the `K` training episodes, the correlated
output policy `π̂` of Algorithm 3 satisfies, for every player `j`,
`V^{†, π̂_{−j}}_{j,1}(s_1) − V^{π̂}_{j,1}(s_1) ≤ C ((H²S/K) Ξ(A, K/S, ι) + √(H⁵Sι/K))`,
with `C` depending only on `c₁`. -/
theorem theorem_6 :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c₁ : ℝ, ∃ C : ℝ, ∀ (G : Game), G.Standing →
      ∀ (alg : ∀ j, BanditRule (G.A j)), (∀ j, (alg j).Valid) →
      ∀ (ξ : ℕ → ℕ → ℝ → ℝ) (Ξ : ℕ → ℝ → ℝ → ℝ),
        (∀ j, Assumption1 G.H (alg j) ξ) →
        (∀ B B' t x, 0 < x → B ≤ B' → ξ B t x ≤ ξ B' t x) →
        (∀ B (t : ℕ) x, 0 < x → ∑ t' ∈ Finset.Icc 1 t, ξ B t' x ≤ Ξ B t x) →
        (∀ B x, 0 < x → ConcaveOn ℝ (Set.Ici 0) (fun t => Ξ B t x)) →
      ∀ (β : Fin G.m → ℕ → ℝ), (∀ j t, 0 ≤ β j t) →
      ∀ (δ : ℝ), 0 < δ → δ < 1 → ∀ K : ℕ, 1 ≤ K →
        (∀ j t, 1 ≤ t → t ≤ K →
          c₀ * bonusScale G ξ (G.A j) (iota G K δ) t ≤
              ∑ i ∈ Finset.Icc 1 t, lrW G.H t i * β j i ∧
            ∑ i ∈ Finset.Icc 1 t, lrW G.H t i * β j i ≤
              c₁ * bonusScale G ξ (G.A j) (iota G K δ) t) →
        1 - δ ≤ trainProb G alg β K (fun τ => ∀ j : Fin G.m,
          brValTop G alg β τ j - outValTop G alg β τ j ≤
            C * ((G.H : ℝ) ^ 2 * G.S / K * Ξ G.Amax ((K : ℝ) / G.S) (iota G K δ) +
              Real.sqrt ((G.H : ℝ) ^ 5 * G.S * iota G K δ / K))) := by sorry

end VLearning.CCE
