-- Prove2me | Theorems.Thm_QueueBandit_QUCB_lemma_15
-- name    : QueueBandit.QUCB.lemma_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:40:17.582199+00:00
-- url     : https://prove2.me/theorems/7b0879d2-dd7a-452a-bf46-9700a1f613e0
-- title:
--   Lemma 15, p. 32 — P[max_{1≤s≤t₂} Σ_{l=t₂−s+1}^{t₂} (A_u(l) − R_{uk*_u}(l)) ≥ 2 log t/ε_u] ≤ 1/t³
-- statement:
--   Throughout, $(\lambda,\mu)$ is an instance of the $U\times K$ switch satisfying Assumptions 1 and 2 (entries in $[0,1]$, unique optimal matching $k^*$, $\epsilon_u=\mu^*_u-\lambda_u>0$), $2\le K$ and $U\le K$, and $\mathbb P$ is the law of the system started from the stationary law $\pi_{(\lambda,\mu^*)}$ of Assumption 3. For every queue $u$ and natural numbers $t_2,t$ with $1\le t_2\le t$,
--   $$\mathbb P\Big[\max_{1\le s\le t_2}\Big\{\sum_{l=t_2-s+1}^{t_2}A_u(l)-R_{uk^*_u}(l)\Big\}\ \ge\ \frac{2\log t}{\epsilon_u}\Big]\ \le\ \frac1{t^3}.$$
--
--   The arrivals minus the optimal services form a random walk with drift $-\epsilon_u$; the lemma bounds all its suffix sums at once, which controls how much queue $u$ can build up within a regenerative cycle (Lemma 16).
--
--   **Formalization Note** The maximum is a `Finset.sup'` over $s\in\{1,\dots,t_2\}$, nonempty since $t_2\ge1$. The proof's "mean $\epsilon_u$" should read $-\epsilon_u$ (paper.md slip 12); the statement is unaffected.
-- source:
--   Krishnasamy, Sen, Johari and Shakkottai, arXiv:1604.06377v4, p. 32, Lemma 15; proof p. 32 (Hoeffding)

import Mathlib
import Definitions.Def_QueueBandit_QUCB_Model
import Definitions.Def_QueueBandit_QUCB_Algorithm1

namespace QueueBandit.QUCB

theorem lemma_15 {U K : ℕ} (hUK : U ≤ K) (hK : 2 ≤ K) (I : Instance U K)
    (u : Fin U) (t t₂ : ℕ) (h₁ : 1 ≤ t₂) (h₂ : t₂ ≤ t) :
    I.P.real {ω : Ω U K | 2 * Real.log t / I.eps u ≤
        (Finset.Icc 1 t₂).sup' (Finset.nonempty_Icc.mpr h₁) (fun s =>
          ∑ l ∈ Finset.Ioc (t₂ - s) t₂, ((I.A u l ω : ℝ) - (I.R u (I.kstar u) l ω : ℝ)))} ≤
      1 / (t : ℝ) ^ 3 := by sorry

end QueueBandit.QUCB
