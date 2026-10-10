-- Prove2me | Theorems.Thm_QueueBandit_QUCB_lemma_11
-- name    : QueueBandit.QUCB.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:40:35.035573+00:00
-- url     : https://prove2.me/theorems/7d64b5be-19aa-4c9e-95ca-df64ca2aa939
-- title:
--   Lemma 11, p. 25 — Q-UCB schedules no sub-optimal matching through Exploit in (w(t), t] except with probability UK/(6t³)
-- statement:
--   Throughout, $(\lambda,\mu)$ is an instance of the $U\times K$ switch satisfying Assumptions 1 and 2 (entries in $[0,1]$, unique optimal matching $k^*$, $\epsilon_u=\mu^*_u-\lambda_u>0$), $2\le K$ and $U\le K$, and $\mathbb P$ is the law of the system started from the stationary law $\pi_{(\lambda,\mu^*)}$ of Assumption 3. Run Q-UCB with any covering family $\mathcal X$ and any tie-breaking rules, let $\beta>1$, $w(t)=t^{1-1/\beta}$ and
--   $$\mathcal E_1=\Big\{\sum_{l=w(t)+1}^{t}\sum_{u\in[U]}\sum_{k\neq k^*_u}\mathsf I_{uk}(l)=0\Big\},$$
--   the event that every exploit slot in $(w(t),t]$ schedules the optimal server for every queue. Then for every natural $t\ge 5800$ with $t\ge\exp\big(4/(\Delta^2(1-1/\beta)^3)\big)$,
--   $$\mathbb P[\mathcal E_1^c]\ \le\ \frac{UK}{6t^3}.$$
--
--   This is the learning half of the argument: in the late stage the UCB indices, fed by forced exploration, identify the optimal matching, so sub-optimal schedules come only from exploration.
--
--   **Formalization Note** This is the Q-UCB part of the lemma ($\tau_1=5800$); the Q-ThS part is not formalized. $K\ge2$ is needed: the page's last numerical step fails at $U=K=1$ (paper.md slip 9). The sum over $l$ ranges over natural $l$ with $w(t)<l\le t$.
-- source:
--   Krishnasamy, Sen, Johari and Shakkottai, arXiv:1604.06377v4, p. 25, Lemma 11 (Q-UCB part); proof pp. 25–27, (6)–(13)

import Mathlib
import Definitions.Def_QueueBandit_QUCB_Model
import Definitions.Def_QueueBandit_QUCB_Algorithm1

namespace QueueBandit.QUCB

theorem lemma_11 {U K : ℕ} (hUK : U ≤ K) (hK : 2 ≤ K) (I : Instance U K)
    (A : QUCBRule U K) (β : ℝ) (hβ : 1 < β) (t : ℕ) (ht : 5800 ≤ t)
    (hΔ : Real.exp (4 / (I.gap ^ 2 * (1 - 1 / β) ^ 3)) ≤ t) :
    I.P.real (A.E1 I β t)ᶜ ≤ (U : ℝ) * K / (6 * (t : ℝ) ^ 3) := by sorry

end QueueBandit.QUCB
