-- Prove2me | Theorems.Thm_PeriodicMAB_Lower_theorem_3
-- name    : PeriodicMAB.Lower.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:08:22.647527+00:00
-- url     : https://prove2.me/theorems/d803a2af-6a47-4e42-8373-7cbd86a3068a
-- title:
--   Theorem 3, p. 24 — every policy that knows the periods has regret ≥ √(T·max_k T_k)/(32e) on some instance of ℰ₃(T₁,…,T_K)
-- statement:
--   Consider the periodic multi-armed bandit with $K \ge 2$ arms and unit-variance Gaussian rewards: if arm $k$ is pulled at epoch $t$, the reward is drawn from $\mathcal N(\mu_{k,t}, 1)$. Let $T$ be the horizon and $T_1, \dots, T_K \ge 1$ integer periods satisfying Assumption 3 with the parameters (7): $T > 4K$, and with $n = \lfloor\sqrt{T/K}\rfloor$ and $g = \lceil\sqrt n\rceil$, $g \ge 2$ and $T_k < n/(2g)$ for every $k$.
--
--   Let $\mathcal E_3(T_1, \dots, T_K)$ be the class of instances whose arm $k$ has mean sequence of minimum period exactly $T_k$, with all means in $[0,1]$ on epochs $1, \dots, T$. Then for every policy $\pi$ there is an instance $\nu \in \mathcal E_3(T_1,\dots,T_K)$ such that
--   $$\mathbb E_\nu[R^\pi_T] \ge \frac{1}{32e}\sqrt{T \max_{k} T_k},$$
--   where $\mathbb E_\nu[R^\pi_T] = \sum_{t=1}^T(\max_k \mu_{k,t} - \mathbb E[\mu_{\pi_t,t}])$ is the expected regret (1).
--
--   Hence $\sup_{\nu \in \mathcal E_3(T_1,\dots,T_K)} \mathbb E_\nu[R^\pi_T] \ge \sqrt{T\max_k T_k}/(32e)$, the paper's Theorem 3. Since $\sqrt{T\max_k T_k} \ge \sqrt{T\sum_k T_k}/\sqrt K$, it shows that the $\tilde O(\sqrt{T\sum_k T_k})$ regret of the paper's two-stage policy is optimal up to logarithmic factors when $K$ is fixed.
--
--   **Formalization Note** The policy is an arbitrary randomized policy (one Markov kernel per round, the platform's `BanditAlgorithm.BanditPolicy`), fixed before the instance; it may therefore depend on $K$, $T$ and the periods, which is the paper's "policy that knows $T_k$". The hypothesis $K \ge 2$ is added (with one arm the regret is $0$). Assumption 3 with (7) is the standing assumption of Appendix B.4 (p. 46). Arms are 0-based; no arm is assumed to carry the largest period.
-- source:
--   Chen, Wang and Wang, Learning and Optimization with Seasonal Patterns, arXiv:2005.08088v4, p. 24, Theorem 3 (proof pp. 47–49, (B-47)–(B-49)); Assumption 3 and (7), p. 12; standing assumptions of B.4, p. 46

import Mathlib
import Definitions.Def_BanditPolicy
import Definitions.Def_GaussianBandit
import Definitions.Def_PeriodicMAB_Lower_Model

namespace PeriodicMAB.Lower

open BanditAlgorithm

theorem theorem_3 (K T : ℕ) [NeZero K] (Tper : Fin K → ℕ) (hK : 2 ≤ K)
    (hTper : ∀ k, 1 ≤ Tper k) (hA3 : Assumption3 K T Tper) (π : BanditPolicy K) :
    ∃ μ : Fin K → ℕ → ℝ, InE3 T Tper μ ∧
      Real.sqrt ((T : ℝ) * ((Finset.univ.sup Tper : ℕ) : ℝ)) / (32 * Real.exp 1) ≤
        periodicRegret μ π T := by sorry

end PeriodicMAB.Lower
