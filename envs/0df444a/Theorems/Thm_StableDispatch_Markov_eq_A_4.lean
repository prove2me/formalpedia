-- Prove2me | Theorems.Thm_StableDispatch_Markov_eq_A_4
-- name    : StableDispatch.Markov.eq_A_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:41:59.087986+00:00
-- url     : https://prove2.me/theorems/989f3957-cba2-4cd3-97f5-f702a69c42e2
-- title:
--   (A.4), p. 16 — the drift of Ξ2 = Σj qj² equals λn(2qi + 1) − Σj µj(2qj − 1)1[1,∞)(qj) and is at most λn(2qi + 1) + n − 2Σj µjqj
-- statement:
--   Fix $n$, $\lambda\in(0,1)$, $\alpha_n>0$ and $\mu\in\Sigma_n$, and let $r$ be the transition rates of the chain $(Q(\cdot),I(\cdot))$ of the single-ID policy, with $\Xi_2(q,i)=\sum_{j=1}^nq_j^2$. For every state $(q,i)$, the series below converges and
--
--   $$\sum_{(q',i')\in\mathbb Z_+^n\times\{1,\dots,n\}}\big[\Xi_2(q',i')-\Xi_2(q,i)\big]r_{(q,i)\to(q',i')}=\lambda n(2q_i+1)-\sum_{j=1}^n\mu_j(2q_j-1)\mathbb 1_{[1,\infty)}(q_j)$$
--   $$=\lambda n(2q_i+1)+\sum_{j=1}^n\mu_j\mathbb 1_{[1,\infty)}(q_j)-2\sum_{j=1}^n\mu_jq_j\le\lambda n(2q_i+1)+n-2\sum_{j=1}^n\mu_jq_j .$$
--
--   The last inequality uses $\mu\in\Sigma_n$, i.e. $\sum_j\mu_j=n$ (A.5). This is the drift of the quadratic part of the Lyapunov function.
--
--   **Formalization Note.** The sum runs over all states, including $(q,i)$ itself, where the summand is $0$; it is stated as a `HasSum`.
--
--   Differences from the source:
--   - encoding: Σ over all (q′, i′) of [Ξ2(q′, i′) − Ξ2(q, i)] r → `HasSum` of the family y ↦ (Ξ2(y) − Ξ2(x))·Q(x, y) with Q the generator; reason: same sum, with convergence made explicit (the diagonal term is 0)
--   - encoding: servers {1, …, n} → `Fin n` (0-based); reason: Lean convention, same instances
-- source:
--   Gamarnik, Tsitsiklis, Zubeldia, Stability, Memory, and Messaging Trade-Offs in Heterogeneous Service Systems, arXiv:2007.07219v1, p. 16, (A.4), (A.5)

import Mathlib
import Definitions.Def_MatrixAnalytic_Tree_Process
import Definitions.Def_StableDispatch_Markov_Setting

namespace StableDispatch.Markov

theorem eq_A_4 (n : ℕ) (lam α : ℝ) (μ : Fin n → ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hα : 0 < α) (hμ : μ ∈ Sigma n) (q : Fin n → ℕ) (i : Fin n) :
    HasSum (fun y : State n => (Xi2 y - Xi2 (q, i)) * gen n lam α μ (q, i) y)
        (lam * n * (2 * (q i : ℝ) + 1)
          - ∑ j, μ j * (2 * (q j : ℝ) - 1) * (if 1 ≤ q j then 1 else 0)) ∧
      lam * n * (2 * (q i : ℝ) + 1)
          - ∑ j, μ j * (2 * (q j : ℝ) - 1) * (if 1 ≤ q j then 1 else 0)
        = lam * n * (2 * (q i : ℝ) + 1) + ∑ j, μ j * (if 1 ≤ q j then 1 else 0)
          - 2 * ∑ j, μ j * (q j : ℝ) ∧
      lam * n * (2 * (q i : ℝ) + 1) + ∑ j, μ j * (if 1 ≤ q j then 1 else 0)
          - 2 * ∑ j, μ j * (q j : ℝ)
        ≤ lam * n * (2 * (q i : ℝ) + 1) + n - 2 * ∑ j, μ j * (q j : ℝ) := by sorry

end StableDispatch.Markov
