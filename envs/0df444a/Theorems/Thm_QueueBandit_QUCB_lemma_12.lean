-- Prove2me | Theorems.Thm_QueueBandit_QUCB_lemma_12
-- name    : QueueBandit.QUCB.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:40:06.299346+00:00
-- url     : https://prove2.me/theorems/0a982ac2-e91f-4dc2-85c1-ee66441c1a17
-- title:
--   Lemma 12, p. 29 — pathwise, Q_u(t) − Q*_u(t) ≤ Σ over the current regenerative cycle of (E(l) + Σ_{k≠k*_u} I_uk(l))
-- statement:
--   Throughout, $(\lambda,\mu)$ is an instance of the $U\times K$ switch satisfying Assumptions 1 and 2 (entries in $[0,1]$, unique optimal matching $k^*$, $\epsilon_u=\mu^*_u-\lambda_u>0$), $2\le K$ and $U\le K$, and $\mathbb P$ is the law of the system started from the stationary law $\pi_{(\lambda,\mu^*)}$ of Assumption 3. Run Q-UCB with any covering family and tie-breaking rules, and let $B_u(t)=\min\{s\ge0:Q_u(t-s)=0\}$ be the time elapsed since queue $u$ was last empty. Then for every $t\ge1$ and every sample point,
--   $$Q_u(t)-Q^*_u(t)\ \le\ \sum_{l=t-B_u(t)+1}^{t}\Big(\mathsf E(l)+\sum_{k\neq k^*_u}\mathsf I_{uk}(l)\Big).$$
--
--   The excess of the queue over the genie queue is thus charged to the sub-optimal schedules (explore slots and sub-optimal exploit slots) of the current regenerative cycle; this reduces the regret bound to bounding the cycle length and the number of such schedules.
--
--   **Formalization Note** The statement is pathwise (for every $\omega$). It uses the coupling $Q^*_u(0)=Q_u(0)$ with shared arrivals and services, and $B_u(t)=t$ when queue $u$ was never empty on $[0,t]$ (paper.md slips 6 and 7). The inequality is stated in $\mathbb Z$.
-- source:
--   Krishnasamy, Sen, Johari and Shakkottai, arXiv:1604.06377v4, p. 29, Lemma 12 and the definition of B_u(t); proof pp. 29–30

import Mathlib
import Definitions.Def_QueueBandit_QUCB_Model
import Definitions.Def_QueueBandit_QUCB_Algorithm1

namespace QueueBandit.QUCB

theorem lemma_12 {U K : ℕ} (hUK : U ≤ K) (hK : 2 ≤ K) (I : Instance U K)
    (A : QUCBRule U K) (u : Fin U) (t : ℕ) (ht : 1 ≤ t) (ω : Ω U K) :
    (A.Q I u t ω : ℤ) - (I.Qstar u t ω : ℤ) ≤
      ∑ l ∈ Finset.Ioc (t - A.B I u t ω) t,
        ((explore l ω : ℤ) +
          ∑ k ∈ Finset.univ.filter (fun k => k ≠ I.kstar u), (A.exploit I u k l ω : ℤ)) := by sorry

end QueueBandit.QUCB
