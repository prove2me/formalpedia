-- Prove2me | Theorems.Thm_QueueBandit_QUCB_theorem_5
-- name    : QueueBandit.QUCB.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:42:37.123157+00:00
-- url     : https://prove2.me/theorems/425f9474-4539-48a3-a2c4-ca471fdfa46e
-- title:
--   Theorem 5, p. 16 — Q-UCB has Ψ_u(t) ≤ 6K v_u(t) log² t/t + (24.004 + UK)/(6t²) for t ≥ 5800 in the late-stage range
-- statement:
--   Consider the switch with $U$ queues and $K$ servers, $2\le K$, $U\le K$, and an instance $(\lambda,\mu)$ with a unique optimal matching $k^*$ (Assumption 1) and $\epsilon_u=\mu^*_u-\lambda_u>0$ for all $u$ (Assumption 2), started from the stationary law of the genie queues (Assumption 3). Run Q-UCB (Algorithm 1) with any covering family of explore matchings and any tie-breaking rules. For a queue $u$ and a fixed $\beta>1$ let
--   $$w(t)=t^{1-1/\beta},\qquad v'_u(t)=\frac{6K}{\epsilon_u}w(t),\qquad v_u(t)=\frac{24}{\epsilon_u^2}\log t+\frac{60K}{\epsilon_u}\frac{v'_u(t)\log^2t}{t}.$$
--   Then for every natural $t\ge\tau_1=5800$ such that $t\ge\exp\big(4/(\Delta^2(1-1/\beta)^3)\big)$, $w(t)/\log t\ge2/\epsilon_u$ and $v_u(t)+v'_u(t)\le t/2$, the queue-regret $\Psi_u(t)=\mathbb E[Q_u(t)-Q^*_u(t)]$ is well defined and
--   $$\Psi_u(t)\ \le\ 6K\frac{v_u(t)\log^2t}{t}+\frac{24.004+UK}{6t^2}.$$
--
--   This is the paper's upper bound for the late stage: once the algorithm has learned the optimal matching, the queue-regret of Q-UCB decays like $O(K\log^3t/(\epsilon_u^2t))$, within a polylogarithmic factor of the $\Omega(1/t)$ lower bound for consistent policies.
--
--   **Formalization Note** This is the statement for Algorithm 1 (Q-UCB); the Q-ThS part ("resp., Algorithm 2", $t\ge\tau_2$) is not formalized. $K\ge2$ is added (for $K=1$ the gap $\Delta$ is a minimum over the empty set, and the constant $24.004$ absorbs $t\cdot t^{-2K}$ only for $K\ge2$; paper.md slip 9). The conclusion also asserts that $Q_u(t)-Q^*_u(t)$ is integrable, so that $\Psi_u(t)$ is a genuine expectation rather than a default value. The systems are coupled ($Q^*(0)=Q(0)$, shared arrivals and services), which does not change $\Psi_u(t)$.
-- source:
--   Krishnasamy, Sen, Johari and Shakkottai, arXiv:1604.06377v4, p. 16, Theorem 5 (Algorithm 1); proof pp. 24–35

import Mathlib
import Definitions.Def_QueueBandit_QUCB_Model
import Definitions.Def_QueueBandit_QUCB_Algorithm1

namespace QueueBandit.QUCB

theorem theorem_5 {U K : ℕ} (hUK : U ≤ K) (hK : 2 ≤ K) (I : Instance U K)
    (A : QUCBRule U K) (β : ℝ) (hβ : 1 < β) (u : Fin U) (t : ℕ) (ht : 5800 ≤ t)
    (hΔ : Real.exp (4 / (I.gap ^ 2 * (1 - 1 / β) ^ 3)) ≤ t)
    (hw : 2 / I.eps u ≤ w β t / Real.log t) (hv : I.v β u t + I.vPrime β u t ≤ (t : ℝ) / 2) :
    MeasureTheory.Integrable (fun ω => (A.Q I u t ω : ℝ) - (I.Qstar u t ω : ℝ)) I.P ∧
      A.Psi I u t ≤
        6 * K * (I.v β u t * Real.log t ^ 2) / t + (24.004 + U * K) / (6 * (t : ℝ) ^ 2) := by sorry

end QueueBandit.QUCB
