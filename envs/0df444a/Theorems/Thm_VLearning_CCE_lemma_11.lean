-- Prove2me | Theorems.Thm_VLearning_CCE_lemma_11
-- name    : VLearning.CCE.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:29:41.681114+00:00
-- url     : https://prove2.me/theorems/68bb4719-e431-45a1-968e-258580ceeee5
-- title:
--   Lemma 11, p. 19, (9) — Ṽ^k_{j,h}(s) as an α-weighted sum of earlier updates
-- statement:
--   Consider a run of V-learning, an episode $k$, a step $h$, a state $s$ and a player $j$. Let $t=N^k_h(s)$ be the number of times $s$ was visited at step $h$ before episode $k$, in the episodes $k^1<\dots<k^t<k$. Then
--   $$\tilde V^k_{j,h}(s)=\alpha^0_t(H-h+1)+\sum_{i=1}^t\alpha^i_t\Big[r_{j,h}(s,\boldsymbol a^{k^i}_h)+V^{k^i}_{j,h+1}(s^{k^i}_{h+1})+\beta_{j,i}\Big].$$
--
--   The identity turns the incremental update of Algorithm 1 into a weighted average, which is the form used by the optimism and gap arguments.
--
--   **Formalization Note** The identity holds for every sequence of episodes, with no hypothesis. Steps are 0-based, so $H-h+1$ is `H - h.val`, and $V^{k^i}_{j,h+1}(s^{k^i}_{h+1})$ is $0$ at the last step.
-- source:
--   Jin, Liu, Wang & Yu, V-Learning—A Simple, Efficient, Decentralized Algorithm for Multiagent RL, arXiv:2110.14555v1, p. 19, Lemma 11, (9)

import Mathlib
import Definitions.Def_VLearning_CCE_Model

namespace VLearning.CCE

open RunState

/-- Lemma 11 (p. 19), (9): `Ṽ^k_{j,h}(s)` unrolled as a weighted sum of earlier updates. Steps are
0-based, so the paper's `H − h + 1` is `H - h.val`, and `V^{k^i}_{j,h+1}(s^{k^i}_{h+1})` is `0` at the
last step. -/
theorem lemma_11 (G : Game) (β : Fin G.m → ℕ → ℝ) (K : ℕ) (τ : Fin K → Episode G) (k : Fin K)
    (h : Fin G.H) (s : Fin G.S) (j : Fin G.m) :
    (runState G β τ k.val).vTildeUp j h s =
      lrW G.H ((runState G β τ k.val).visits h s).length 0 * ((G.H : ℝ) - h.val) +
      ∑ i : Fin ((runState G β τ k.val).visits h s).length,
        lrW G.H ((runState G β τ k.val).visits h s).length (i.val + 1) *
          (G.r j h s (τ (((runState G β τ k.val).visits h s).get i) h).2 +
            (runState G β τ (((runState G β τ k.val).visits h s).get i).val).vUpAfter j
              (τ (((runState G β τ k.val).visits h s).get i)) h +
            β j (i.val + 1)) := by sorry

end VLearning.CCE
