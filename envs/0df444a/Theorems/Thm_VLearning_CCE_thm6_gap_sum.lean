-- Prove2me | Theorems.Thm_VLearning_CCE_thm6_gap_sum
-- name    : VLearning.CCE.thm6_gap_sum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:29:41.919652+00:00
-- url     : https://prove2.me/theorems/fc44332b-c3e1-452e-ae10-a6d72622d1e4
-- title:
--   Proof of Theorem 6, p. 24 — Σ_k max_j [V^k_{1,j} − V̲^k_{1,j}](s_1) ≤ O(H²SΞ(A, K/S, ι) + √(H⁵SKι))
-- statement:
--   For every constant $c_1>0$ there is $C$ with the following property. Consider any sequence of $K\ge1$ episodes of V-learning, each starting at $s_1$, on a Markov game satisfying the standing assumptions with $mHSAK\ge2$. Let $\xi\ge0$ be non-decreasing in $B$, and let $\Xi(B,t,x)\ge\sum_{t'=1}^t\xi(B,t',x)$ be concave in $t\ge0$ (for $x>0$). Let $\delta\in(0,1)$, $\iota=\log(mHSAK/\delta)$, and let the bonuses be nonnegative with $\sum_{i=1}^t\alpha^i_t\beta_{j,i}\le c_1(H\xi(A_j,t,\iota)+\sqrt{H^3\iota/t})$ for every player $j$ and $t\in[K]$. Then
--   $$\sum_{k=1}^K\max_j\big[V^k_{j,1}-\underline V^k_{j,1}\big](s_1)\le C\Big(H^2S\,\Xi(A,K/S,\iota)+\sqrt{H^5SK\iota}\Big).$$
--
--   Combined with optimism and pessimism, this sum bounds $K$ times the CCE gap of the output policy.
--
--   **Formalization Note** The statement is deterministic. The hypothesis $mHSAK\ge2$ is added: the printed recursion ends with an $eSH^2$ term that the display drops, and without the hypothesis the display fails at $m=H=S=A=K=1$, $\Xi\equiv0$, $\delta\to1$ (left side $1$, right side $\to0$). The hypothesis $\xi\ge0$ follows from Assumption 1, which this statement does not assume. Only the upper half of the bonus condition is used.
-- source:
--   Jin, Liu, Wang & Yu, V-Learning—A Simple, Efficient, Decentralized Algorithm for Multiagent RL, arXiv:2110.14555v1, p. 24, proof of Theorem 6, first display

import Mathlib
import Definitions.Def_VLearning_CCE_Model

namespace VLearning.CCE

/-- Proof of Theorem 6 (p. 24), first display: for every training run whose episodes start at
`s_1`, `∑_k max_j [V^k_{j,1} − V̲^k_{j,1}](s_1) ≤ C (H²SΞ(A, K/S, ι) + √(H⁵SKι))`, where `C` depends
only on the upper constant `c₁` of the bonus. The hypothesis `2 ≤ mHSAK` is added: without it the
display fails at `m = H = S = A = K = 1`, `Ξ ≡ 0`, `δ → 1`. -/
theorem thm6_gap_sum :
    ∀ c₁ : ℝ, 0 < c₁ → ∃ C : ℝ, ∀ (G : Game), G.Standing →
      ∀ (ξ : ℕ → ℕ → ℝ → ℝ) (Ξ : ℕ → ℝ → ℝ → ℝ),
        (∀ B t x, 0 < x → 0 ≤ ξ B t x) →
        (∀ B B' t x, 0 < x → B ≤ B' → ξ B t x ≤ ξ B' t x) →
        (∀ B (t : ℕ) x, 0 < x → ∑ t' ∈ Finset.Icc 1 t, ξ B t' x ≤ Ξ B t x) →
        (∀ B x, 0 < x → ConcaveOn ℝ (Set.Ici 0) (fun t => Ξ B t x)) →
      ∀ (β : Fin G.m → ℕ → ℝ), (∀ j t, 0 ≤ β j t) →
      ∀ (δ : ℝ), 0 < δ → δ < 1 → ∀ K : ℕ, 1 ≤ K →
        2 ≤ G.m * G.H * G.S * G.Amax * K →
        (∀ j t, 1 ≤ t → t ≤ K →
          ∑ i ∈ Finset.Icc 1 t, lrW G.H t i * β j i ≤
            c₁ * bonusScale G ξ (G.A j) (iota G K δ) t) →
        ∀ (τ : Fin K → Episode G), (∀ (k : Fin K) (h : Fin G.H), h.val = 0 → (τ k h).1 = G.s1) →
          ∑ k : Fin K, gapAt G β τ k 0 ≤
            C * ((G.H : ℝ) ^ 2 * G.S * Ξ G.Amax ((K : ℝ) / G.S) (iota G K δ) +
              Real.sqrt ((G.H : ℝ) ^ 5 * G.S * K * iota G K δ)) := by sorry

end VLearning.CCE
