-- Prove2me | Theorems.Thm_TimeDepFolk_Asymptotic_lemma_5_2
-- name    : TimeDepFolk.Asymptotic.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:19:16.088605+00:00
-- url     : https://prove2.me/theorems/19edd820-60fd-46d1-93b9-3aed2a96b1b2
-- title:
--   Lemma 5.2, p. 25 — α(L,S) = Σ_{t>L(η,k,T′)+1}^{S+1} θ^k_t[T′] ≤ 8η/κ
-- statement:
--   Let $\theta$ be an evaluation and $\kappa,\eta>0$ with $\eta<\kappa/8$. Let $T<T'$ be stages, $L=L(\eta,k,T)$ and $L'=L(\eta,k,T')$ positive integers satisfying (5.1) at $T$ and at $T'$ respectively, and let $S=T+L-T'\ge0$ be the number of periods from stage $T'+1$ to the end of the punishment phase that started at $T$. If $L'<S$ (Case Two), then
--   $$\alpha(L,S)=\sum_{t=L'+2}^{S+1}\theta_t[T']\le\frac{8\eta}{\kappa}.$$
--
--   The lemma bounds the weight of the part of an interrupted punishment that lies beyond the new punishment, which is the remaining term in the incentive check (5.7) for a punisher who deviates.
--
--   **Formalization Note.** Stages are 0-based on both $T=n+1$ and $T'=n'+1$; the relation $n'+S=n+L$ is the page's $T'+S=T+L$, and $T<T'$ is $n<n'$. The paper's range $t\in\{L'+2,\dots,S+1\}$ of $\theta[T']$ is `Finset.Ico (L' + 1) (S + 1)` of `cont θ.θ n'`. The page has $T'\in\{T+1,\dots,T+L\}$, which is $n<n'$ together with $S\ge0$. If the tail sum at $T'$ were $0$, every continuation weight would be $0$ and the bound would hold trivially; (5.1) at $T$ forces the tail at $T$ to be positive.
-- source:
--   X. Li, The folk theorem for repeated games with time-dependent discounting, SSRN Working Paper 3407197 (version of August 16, 2019), p. 25, Lemma 5.2 (S and Case Two p. 23; α(L,S) p. 25)

import Mathlib
import Definitions.Def_TimeDepFolk_Asymptotic_Model

namespace TimeDepFolk.Asymptotic

theorem lemma_5_2 (θ : Evaluation) (κ η : ℝ) (hκ : 0 < κ) (hη : 0 < η) (hηκ : η < κ / 8)
    (n n' L L' S : ℕ) (hL : IsPunLength θ κ η n L) (hL' : IsPunLength θ κ η n' L')
    (hn' : n < n') (hS : n' + S = n + L) (hcase : L' < S) :
    ∑ t ∈ Finset.Ico (L' + 1) (S + 1), cont θ.θ n' t ≤ 8 * η / κ := by sorry

end TimeDepFolk.Asymptotic
