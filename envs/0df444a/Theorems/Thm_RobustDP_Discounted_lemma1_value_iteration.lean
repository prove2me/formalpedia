-- Prove2me | Theorems.Thm_RobustDP_Discounted_lemma1_value_iteration
-- name    : RobustDP.Discounted.lemma1_value_iteration
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:45:27.993034+00:00
-- url     : https://prove2.me/theorems/2442aefd-f718-4ea1-aec1-7e43c8fee5aa
-- title:
--   Lemma 1 (first claim) — robust value iteration stops, and its output is within ε/4 of V*_λ
-- statement:
--   Let $(\mathcal S,\mathcal A,\mathcal P,r,\lambda)$ be a discounted ambiguous MDP, let $\mathcal T$ be the operator of (30), let $V_0$ be bounded and $\epsilon>0$, and let $V_k=\mathcal T^kV_0$. The robust value iteration algorithm of Figure 1 returns $\tilde V=V_{K+1}$, where $K$ is the first index with
--   $$\|V_{K+1}-V_K\|<\frac{1-\lambda}{4\lambda}\,\epsilon .$$
--   Then such a $K$ exists (the algorithm stops), and for the first such $K$,
--   $$\|\tilde V-V^*_\lambda\|=\|V_{K+1}-V^*_\lambda\|\le\frac{\epsilon}{4}.$$
--
--   This is the approximation guarantee of robust value iteration.
--
--   **Formalization Note** The algorithm is encoded by its iterates: the stopping index $K$ is characterized by the stopping test holding at $K$ and failing at every $k<K$. Only the first sentence of Lemma 1 is stated. Its second claim (an $\epsilon/2$-greedy rule against $\tilde V$ is $\epsilon$-optimal) is false as printed and is not part of the mission. Figure 1's header says $\epsilon/2$; the Lemma's $\epsilon/4$ is used.
-- source:
--   Iyengar, Robust dynamic programming, CORC Tech Report TR-2002-07 (rev. May 4, 2004), p. 12, Lemma 1 (first sentence); algorithm in Figure 1, p. 11

import Mathlib
import Definitions.Def_RobustDP_Discounted_Model
import Definitions.Def_RobustDP_Discounted_Value
import Definitions.Def_RobustDP_Discounted_Bellman

namespace RobustDP.Discounted

theorem lemma1_value_iteration {S A : Type*} [Countable S] [Countable A] (M : Model S A)
    (V₀ : S → ℝ) (hV₀ : IsBounded V₀) (ε : ℝ) (hε : 0 < ε) :
    let Vk : ℕ → S → ℝ := fun k => (T M)^[k] V₀
    let c : ℝ := (1 - M.lam) / (4 * M.lam) * ε
    (∃ K, supNorm (fun s => Vk (K + 1) s - Vk K s) < c) ∧
      ∀ K, supNorm (fun s => Vk (K + 1) s - Vk K s) < c →
        (∀ k < K, c ≤ supNorm (fun s => Vk (k + 1) s - Vk k s)) →
        supNorm (fun s => Vk (K + 1) s - Vstar M s) ≤ ε / 4 := by sorry

end RobustDP.Discounted
