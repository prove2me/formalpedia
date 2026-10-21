-- Prove2me | Theorems.Thm_TradingFavors_Existence_lemma_A_1
-- name    : TradingFavors.Existence.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:28:22.073648+00:00
-- url     : https://prove2.me/theorems/a950a596-107a-4ea9-b046-a67de3f02d55
-- title:
--   Lemma A.1, p. A3 (PDF 33) — a deviation to no collaboration at one balance lowers the deviator's payoff
-- statement:
--   Fix parameters satisfying the standing assumptions, a profile $\sigma$, a set $K\subseteq\mathbb Z$ on which condition (4) holds for both firms, and $k\in K$.
--
--   1. If $\sigma_1(k)=0$, let $\tilde\sigma$ agree with $\sigma$ except that $\tilde\sigma_1(k)=1$. Then $\pi_1(x_1,x_2,k'\mid\tilde\sigma)\le\pi_1(x_1,x_2,k'\mid\sigma)$ for every state $(x_1,x_2,k')$, with strict inequality at every state from which the state $(x_1,x_2,k)=(0,1,k)$ can be reached through positive-rate transitions of the chain under $\sigma$ (including that state itself).
--   2. If $\sigma_2(k)=0$, the same holds for firm 2 with $\tilde\sigma_2(k)=1$, its payoff $\pi_2$, and the target state $x_2=0$, $x_1=1$ at balance $k$.
--
--   Refusing a single favor that the equilibrium prescribes can only hurt the firm that refuses.
--
--   **Formalization Note** The page assumes that $\sigma$ is a TFE; the statement only assumes (4) on a set $K$ containing $k$, which is what the proof uses and what is needed when the lemma is applied to $\sigma^L$, which satisfies (4) on its core region only (see the core-region note of Proposition 5). "Can transit to the state with positive probability" is the reflexive–transitive closure of the one-step positive-rate transition relation under $\sigma$ (the transitions out of the target are the only ones that differ under $\tilde\sigma$).
-- source:
--   Hu & Caldentey, Trust and Reciprocity in Firms’ Capacity Sharing, SSRN 4348127 (version of February 6, 2023), p. A3 (PDF 33), Lemma A.1

import Mathlib
import Definitions.Def_TradingFavors_Existence_Model

namespace TradingFavors.Existence

theorem lemma_A_1 (θ : Params) (hθ : θ.Standing) (σ : Profile) (K : Set ℤ)
    (hσ : IsTFEOn θ σ K) (k : ℤ) (hk : k ∈ K) :
    (σ.s1 k = 0 →
      (∀ s : State, pay1 θ ⟨Function.update σ.s1 k 1, σ.s2⟩ s ≤ pay1 θ σ s) ∧
      (∀ s : State, Relation.ReflTransGen (Trans σ) s (0, 1, k) →
        pay1 θ ⟨Function.update σ.s1 k 1, σ.s2⟩ s < pay1 θ σ s)) ∧
    (σ.s2 k = 0 →
      (∀ s : State, pay2 θ ⟨σ.s1, Function.update σ.s2 k 1⟩ s ≤ pay2 θ σ s) ∧
      (∀ s : State, Relation.ReflTransGen (Trans σ) s (1, 0, k) →
        pay2 θ ⟨σ.s1, Function.update σ.s2 k 1⟩ s < pay2 θ σ s)) := by sorry

end TradingFavors.Existence
