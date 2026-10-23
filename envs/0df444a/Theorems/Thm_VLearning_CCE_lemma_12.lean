-- Prove2me | Theorems.Thm_VLearning_CCE_lemma_12
-- name    : VLearning.CCE.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:29:39.10168+00:00
-- url     : https://prove2.me/theorems/107b6553-813d-4a39-a66d-6930a80d6253
-- title:
--   Lemma 12, p. 20 — under Assumption 1, w.p. ≥ 1 − δ, the α-weighted regret of every (s, h)-bandit is at most Hξ(A_j, t, ι)
-- statement:
--   Consider $m$ players running V-learning for $K\ge1$ episodes on a Markov game satisfying the standing assumptions, each with a valid bandit rule satisfying Assumption 1 with the function $\xi$, and with nonnegative bonuses. Let $\delta\in(0,1)$ and $\iota=\log(mHSAK/\delta)$. With probability at least $1-\delta$ over the training run, for every state $s$, step $h$, episode $k\in[K]$ and player $j$, with $t=N^k_h(s)$ and visit episodes $k^1<\dots<k^t<k$,
--   $$\max_{\mu}\sum_{i=1}^t\alpha^i_t\,\mathbb D_{\mu\times\pi^{k^i}_{-j,h}}\big(r_{j,h}+\mathbb P_hV^{k^i}_{j,h+1}\big)(s)-\sum_{i=1}^t\alpha^i_t\,\mathbb D_{\pi^{k^i}_h}\big(r_{j,h}+\mathbb P_hV^{k^i}_{j,h+1}\big)(s)\le H\xi(A_j,t,\iota).$$
--   Here $\mathbb D_\pi[Q](s)=\mathbb E_{\boldsymbol a\sim\pi(\cdot\mid s)}[Q(s,\boldsymbol a)]$, $\mathbb P_h[V](s,\boldsymbol a)=\mathbb E_{s'\sim\mathbb P_h(\cdot\mid s,\boldsymbol a)}[V(s')]$, $\mu\times\pi^{k^i}_{-j,h}$ lets player $j$ play $\mu$ and the others their own policies, and $\pi^{k^i}_h$ is the product of all players' policies at the beginning of episode $k^i$.
--
--   This is the bandit guarantee transported to the Markov game: it is the only place where Assumption 1 enters the proof of Theorem 6.
--
--   **Formalization Note** The maximum over distributions $\mu$ on $\mathcal A_j$ is taken over pure actions (the objective is linear in $\mu$). Bonuses are assumed nonnegative, which keeps the bandit losses in $[0,1]$.
-- source:
--   Jin, Liu, Wang & Yu, V-Learning—A Simple, Efficient, Decentralized Algorithm for Multiagent RL, arXiv:2110.14555v1, p. 20, Lemma 12

import Mathlib
import Definitions.Def_VLearning_CCE_Model

namespace VLearning.CCE

open RunState

/-- Lemma 12 (p. 20): under Assumption 1, with probability at least `1 − δ` over the training run,
for every `(s, h, k, j)`, with `t = N^k_h(s)` and earlier visit episodes `k^1 < ⋯ < k^t`,
`max_b ∑_i α^i_t 𝔻_{b × π^{k^i}_{−j,h}}(r_{j,h} + ℙ_h V^{k^i}_{j,h+1})(s)
   − ∑_i α^i_t 𝔻_{π^{k^i}_h}(r_{j,h} + ℙ_h V^{k^i}_{j,h+1})(s) ≤ H ξ(A_j, t, ι)`. -/
theorem lemma_12 (G : Game) (hG : G.Standing) (alg : ∀ j, BanditRule (G.A j))
    (halg : ∀ j, (alg j).Valid) (ξ : ℕ → ℕ → ℝ → ℝ) (hA1 : ∀ j, Assumption1 G.H (alg j) ξ)
    (β : Fin G.m → ℕ → ℝ) (hβ : ∀ j t, 0 ≤ β j t) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (K : ℕ) (hK : 1 ≤ K) :
    1 - δ ≤ trainProb G alg β K (fun τ =>
      ∀ (s : Fin G.S) (h : Fin G.H) (k : Fin K) (j : Fin G.m),
        (⨆ b : Fin (G.A j), ∑ i : Fin ((runState G β τ k.val).visits h s).length,
            lrW G.H ((runState G β τ k.val).visits h s).length (i.val + 1) *
              ∑ a : G.JointAct,
                devProb alg (runState G β τ (((runState G β τ k.val).visits h s).get i).val) j b h s a *
                  qUp (runState G β τ (((runState G β τ k.val).visits h s).get i).val) j h s a) -
          ∑ i : Fin ((runState G β τ k.val).visits h s).length,
            lrW G.H ((runState G β τ k.val).visits h s).length (i.val + 1) *
              ∑ a : G.JointAct,
                jointProb alg (runState G β τ (((runState G β τ k.val).visits h s).get i).val) h s a *
                  qUp (runState G β τ (((runState G β τ k.val).visits h s).get i).val) j h s a
          ≤ (G.H : ℝ) * ξ (G.A j) ((runState G β τ k.val).visits h s).length (iota G K δ)) := by sorry

end VLearning.CCE
