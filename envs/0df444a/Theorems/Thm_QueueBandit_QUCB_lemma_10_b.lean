-- Prove2me | Theorems.Thm_QueueBandit_QUCB_lemma_10_b
-- name    : QueueBandit.QUCB.lemma_10_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:40:20.599451+00:00
-- url     : https://prove2.me/theorems/e0f34e4c-6323-44d4-90c9-212ab292122b
-- title:
--   Lemma 10(b), p. 24 — for t ≥ 5800 the total number of explore slots exceeds K w(t) with probability at most 1/t^{2K}
-- statement:
--   Let $\mathsf E(l)$ be the explore indicators of Q-UCB and $w(t)=t^{1-1/\beta}$ for a fixed $\beta>1$. Throughout, $(\lambda,\mu)$ is an instance of the $U\times K$ switch satisfying Assumptions 1 and 2 (entries in $[0,1]$, unique optimal matching $k^*$, $\epsilon_u=\mu^*_u-\lambda_u>0$), $2\le K$ and $U\le K$, and $\mathbb P$ is the law of the system started from the stationary law $\pi_{(\lambda,\mu^*)}$ of Assumption 3. For every natural $t\ge 5800$ with $\log w(t)\ge(2\log t)^{2/3}$,
--   $$\mathbb P\Big[\sum_{l=1}^{t}\mathsf E(l)>Kw(t)\Big]\ \le\ \frac1{t^{2K}}.$$
--
--   This shows that the event $\mathcal E_2=\{\sum_{l\le t}\mathsf E(l)\le Kw(t)\}$, on which the explore slots are few, holds with overwhelming probability; it supplies the term $1/t^{2K}$ of Theorem 5.
--
--   **Formalization Note** The hypothesis $\log w(t)\ge(2\log t)^{2/3}$ is added. The proof (p. 25) uses $Kw(t)\ge K\exp((2\log t)^{2/3})$, which is (9) of p. 26 and holds in Theorem 5's range $t\ge\exp(4/(\Delta^2(1-1/\beta)^3))$; without it the printed statement fails (e.g. $\beta=1.01$, $t=5800$, where $w(t)\approx1.09$ while $\mathbb E\sum_l\mathsf E(l)$ is of order $K\log^3t$), see paper.md slip 3.
-- source:
--   Krishnasamy, Sen, Johari and Shakkottai, arXiv:1604.06377v4, p. 24, Lemma 10(b); proof p. 25

import Mathlib
import Definitions.Def_QueueBandit_QUCB_Model
import Definitions.Def_QueueBandit_QUCB_Algorithm1

namespace QueueBandit.QUCB

theorem lemma_10_b {U K : ℕ} (hUK : U ≤ K) (hK : 2 ≤ K) (I : Instance U K)
    (β : ℝ) (hβ : 1 < β) (t : ℕ) (ht : 5800 ≤ t)
    (hw : (2 * Real.log t) ^ ((2 : ℝ) / 3) ≤ Real.log (w β t)) :
    I.P.real {ω : Ω U K | (K : ℝ) * w β t < ((∑ l ∈ Finset.Icc 1 t, explore l ω : ℕ) : ℝ)} ≤
      ((t : ℝ) ^ (2 * K))⁻¹ := by sorry

end QueueBandit.QUCB
