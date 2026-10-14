-- Prove2me | Theorems.Thm_PeriodicMAB_Lower_lemma_13
-- name    : PeriodicMAB.Lower.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:08:17.015186+00:00
-- url     : https://prove2.me/theorems/3edc687c-07b9-4ee7-8a2a-20db7b517c9d
-- title:
--   Lemma 13, p. 23 — one periodic arm of minimum period T₁: every policy has regret ≥ √(TT₁)/(16e) on some instance of ℰ₂(T₁)
-- statement:
--   Let $K \ge 2$, let $T$ be the horizon and $T_1 \ge 1$ an integer, and assume that the periods $(T_1, 1, \dots, 1)$ satisfy Assumption 3 with the parameters (7): $T > 4K$, and with $n = \lfloor\sqrt{T/K}\rfloor$ and $g = \lceil\sqrt n\rceil$, $g \ge 2$ and $T_1 < n/(2g)$.
--
--   Then for every policy $\pi$ there is an instance $\nu$ in the class $\mathcal E_2(T_1)$ (unit-variance Gaussian rewards, means in $[0,1]$, first arm with minimum period exactly $T_1$, all other arms stationary), whose arms other than the first all have mean $1/2$, such that
--   $$\mathbb E_\nu[R^\pi_T] \ge \frac{1}{16e}\sqrt{T T_1}.$$
--
--   In particular $\sup_{\nu \in \mathcal E_2(T_1)} \mathbb E_\nu[R^\pi_T] \ge \sqrt{TT_1}/(16e)$, the printed form of Lemma 13. It is the case of Theorem 3 in which only one arm is non-stationary.
--
--   **Formalization Note** The regret is (1), $\sum_{t=1}^T(\max_k \mu_{k,t} - \mathbb E[\mu_{\pi_t,t}])$, under the round-by-round Gaussian history law. The policy is a general randomized policy fixed before the instance, so it may depend on $K$, $T$ and $T_1$ ("knows $T_1$"). "Knows $\mu_k$ for $k \ge 2$" is formalized by fixing those means to $1/2$, as in the proof; the hypothesis $K \ge 2$ is added (with one arm the regret is $0$). Assumption 3 is the standing assumption of Appendix B.4 (p. 46), with the stationary arms given period $1$. The first arm's minimum period must be exactly $T_1$, as printed.
-- source:
--   Chen, Wang and Wang, Learning and Optimization with Seasonal Patterns, arXiv:2005.08088v4, p. 23, Lemma 13 (proof p. 47, (B-46)); Assumption 3 and (7), p. 12

import Mathlib
import Definitions.Def_BanditPolicy
import Definitions.Def_GaussianBandit
import Definitions.Def_PeriodicMAB_Lower_Model

namespace PeriodicMAB.Lower

open BanditAlgorithm

theorem lemma_13 (K T T₁ : ℕ) [NeZero K] (hK : 2 ≤ K) (hT₁ : 1 ≤ T₁)
    (hA3 : Assumption3 K T (Function.update (fun _ ↦ 1) 0 T₁)) (π : BanditPolicy K) :
    ∃ μ : Fin K → ℕ → ℝ, InE2 T T₁ μ ∧ (∀ k, k ≠ 0 → ∀ t, μ k t = 1 / 2) ∧
      Real.sqrt ((T : ℝ) * T₁) / (16 * Real.exp 1) ≤ periodicRegret μ π T := by sorry

end PeriodicMAB.Lower
