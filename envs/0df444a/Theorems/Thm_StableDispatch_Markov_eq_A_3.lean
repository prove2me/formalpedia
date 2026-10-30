-- Prove2me | Theorems.Thm_StableDispatch_Markov_eq_A_3
-- name    : StableDispatch.Markov.eq_A_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:42:14.601446+00:00
-- url     : https://prove2.me/theorems/8011f722-dc8a-434f-b10b-25a730e61769
-- title:
--   (A.3), p. 15 — the drift of Ξ1 = (2µmax/αn)qi equals λn(2µmax/αn) − (2µmax/αn)µi1[1,∞)(qi) − Σj 2µmax(qi − qj)+
-- statement:
--   Fix $n\ge1$, $\lambda\in(0,1)$, $\alpha_n>0$ and $\mu\in\Sigma_n$, and let $r$ be the transition rates of the chain $(Q(\cdot),I(\cdot))$ of the single-ID policy, with $\mu_{\max}=\max_j\mu_j$ and $\Xi_1(q,i)=\frac{2\mu_{\max}}{\alpha_n}q_i$. For every state $(q,i)$, the series below converges and
--
--   $$\sum_{(q',i')\in\mathbb Z_+^n\times\{1,\dots,n\}}\big[\Xi_1(q',i')-\Xi_1(q,i)\big]r_{(q,i)\to(q',i')}=\lambda n\Big(\frac{2\mu_{\max}}{\alpha_n}\Big)-\frac{2\mu_{\max}}{\alpha_n}\mu_i\mathbb 1_{[1,\infty)}(q_i)-\sum_{j=1}^n2\mu_{\max}(q_i-q_j)^+$$
--   $$\le\lambda n\Big(\frac{2\mu_{\max}}{\alpha_n}\Big)-\sum_{j=1}^n2\mu_{\max}(q_i-q_j)^+ ,$$
--   where $x^+=\max\{x,0\}$.
--
--   This is the drift of the memory term of the Lyapunov function; the negative term $-\sum_j2\mu_{\max}(q_i-q_j)^+$ penalizes a stored server whose queue is longer than others.
--
--   **Formalization Note.** The sum runs over all states, including $(q,i)$ itself, where the summand is $0$; it is stated as a `HasSum` so that convergence is part of the claim. The diagonal of the generator is used as the rate $r_{(q,i)\to(q,i)}$, which is harmless because its factor is $0$.
--
--   Differences from the source:
--   - encoding: Σ over all (q′, i′) of [Ξ1(q′, i′) − Ξ1(q, i)] r → `HasSum` of the family y ↦ (Ξ1(y) − Ξ1(x))·Q(x, y) with Q the generator; reason: same sum, with convergence made explicit (the diagonal term is 0)
--   - encoding: n arbitrary → `[NeZero n]`; reason: μ_max is undefined for n = 0 (no servers)
--   - encoding: servers {1, …, n} → `Fin n` (0-based); reason: Lean convention, same instances
-- source:
--   Gamarnik, Tsitsiklis, Zubeldia, Stability, Memory, and Messaging Trade-Offs in Heterogeneous Service Systems, arXiv:2007.07219v1, p. 15, (A.3)

import Mathlib
import Definitions.Def_MatrixAnalytic_Tree_Process
import Definitions.Def_StableDispatch_Markov_Setting

namespace StableDispatch.Markov

theorem eq_A_3 (n : ℕ) [NeZero n] (lam α : ℝ) (μ : Fin n → ℝ) (hlam0 : 0 < lam)
    (hlam1 : lam < 1) (hα : 0 < α) (hμ : μ ∈ Sigma n) (q : Fin n → ℕ) (i : Fin n) :
    HasSum (fun y : State n => (Xi1 μ α y - Xi1 μ α (q, i)) * gen n lam α μ (q, i) y)
        (lam * n * (2 * muMax μ / α) - 2 * muMax μ / α * μ i * (if 1 ≤ q i then 1 else 0)
          - ∑ j, 2 * muMax μ * max ((q i : ℝ) - (q j : ℝ)) 0) ∧
      lam * n * (2 * muMax μ / α) - 2 * muMax μ / α * μ i * (if 1 ≤ q i then 1 else 0)
          - ∑ j, 2 * muMax μ * max ((q i : ℝ) - (q j : ℝ)) 0
        ≤ lam * n * (2 * muMax μ / α) - ∑ j, 2 * muMax μ * max ((q i : ℝ) - (q j : ℝ)) 0 := by sorry

end StableDispatch.Markov
