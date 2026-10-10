-- Prove2me | Theorems.Thm_QueueBandit_QUCB_lemma_16
-- name    : QueueBandit.QUCB.lemma_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:40:25.821622+00:00
-- url     : https://prove2.me/theorems/c4a42d60-15b9-407b-918b-d15a51abbf1d
-- title:
--   Lemma 16, p. 33 — refined queue bound: P[{Q_u(t − v_u(t)) > (2/ε_u + 5) log t + 30K v′_u(t) log² t/t} ∩ ℰ₁ ∩ ℰ₂] ≤ 3/t³ + 1/t⁴
-- statement:
--   Throughout, $(\lambda,\mu)$ is an instance of the $U\times K$ switch satisfying Assumptions 1 and 2 (entries in $[0,1]$, unique optimal matching $k^*$, $\epsilon_u=\mu^*_u-\lambda_u>0$), $2\le K$ and $U\le K$, and $\mathbb P$ is the law of the system started from the stationary law $\pi_{(\lambda,\mu^*)}$ of Assumption 3. Run Q-UCB with any covering family and tie-breaking rules, fix $\beta>1$, let $w(t)=t^{1-1/\beta}$, $v'_u(t)=\frac{6K}{\epsilon_u}w(t)$, and let $v_u$ be an arbitrary natural-valued function of $t$. Then for every $t$ with $w(t)/\log t\ge2/\epsilon_u$ and $v_u(t)+v'_u(t)\le t/2$,
--   $$\mathbb P\Big[\Big\{Q_u(t-v_u(t))>\Big(\frac2{\epsilon_u}+5\Big)\log t+30K\frac{v'_u(t)\log^2t}{t}\Big\}\cap\mathcal E_1\cap\mathcal E_2\Big]\ \le\ \frac3{t^3}+\frac1{t^4}.$$
--
--   This improves the coarse bound $2Kw(t)$ of Lemma 13 to a polylogarithmic one, which then shortens the regenerative cycle in Lemma 17.
--
--   **Formalization Note** $v_u$ is natural-valued, as in Lemma 14 (paper.md slip 8).
-- source:
--   Krishnasamy, Sen, Johari and Shakkottai, arXiv:1604.06377v4, p. 33, Lemma 16; proof p. 33, (20)–(22)

import Mathlib
import Definitions.Def_QueueBandit_QUCB_Model
import Definitions.Def_QueueBandit_QUCB_Algorithm1

namespace QueueBandit.QUCB

theorem lemma_16 {U K : ℕ} (hUK : U ≤ K) (hK : 2 ≤ K) (I : Instance U K)
    (A : QUCBRule U K) (β : ℝ) (hβ : 1 < β) (u : Fin U) (v : ℕ → ℕ) (t : ℕ)
    (hw : 2 / I.eps u ≤ w β t / Real.log t) (hv : (v t : ℝ) + I.vPrime β u t ≤ (t : ℝ) / 2) :
    I.P.real ({ω | (2 / I.eps u + 5) * Real.log t + 30 * K * (I.vPrime β u t * Real.log t ^ 2 / t) <
        (A.Q I u (t - v t) ω : ℝ)} ∩ A.E1 I β t ∩ E2 β t) ≤
      3 / (t : ℝ) ^ 3 + 1 / (t : ℝ) ^ 4 := by sorry

end QueueBandit.QUCB
