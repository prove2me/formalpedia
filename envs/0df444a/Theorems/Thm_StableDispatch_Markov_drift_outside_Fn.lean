-- Prove2me | Theorems.Thm_StableDispatch_Markov_drift_outside_Fn
-- name    : StableDispatch.Markov.drift_outside_Fn
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:42:08.358636+00:00
-- url     : https://prove2.me/theorems/0d531691-bbab-4f33-94cc-14781035009a
-- title:
--   Appendix A, pp. 16–17, with (A.2) — F_n is finite and the drift of Ξ = Ξ1 + Ξ2 is at most −1 at every state outside F_n
-- statement:
--   Fix $n\ge1$, $\lambda\in(0,1)$, $\alpha_n>0$ and $\mu\in\Sigma_n$, and let $r$ be the transition rates of the chain $(Q(\cdot),I(\cdot))$ of the single-ID policy. Let $\Xi=\Xi_1+\Xi_2$ be the Lyapunov function of (A.1) and
--   $$F_n=\Big\{(q,i)\in\mathbb Z_+^n\times\{1,\dots,n\}:\ \sum_{j=1}^nq_j<\frac{\lambda n\big(1+\frac{2\mu_{\max}}{\alpha_n}\big)+n+1}{2\min\{1-\lambda,\mu_{\min}\}}\Big\}\qquad(A.2).$$
--   Then
--
--   1. $F_n$ is a finite set;
--   2. for every state $(q,i)\notin F_n$ the series below converges and
--   $$\sum_{(q',i')\in\mathbb Z_+^n\times\{1,\dots,n\}}\big[\Xi(q',i')-\Xi(q,i)\big]r_{(q,i)\to(q',i')}\le-1 .$$
--
--   Together with irreducibility and the finiteness of the $\Xi$-weighted exit rates, this is the drift condition of the Foster–Lyapunov criterion, from which the positive recurrence of $(Q(\cdot),I(\cdot))$, and hence Theorem 2.1, follows.
--
--   **Formalization Note.** The sum runs over all states, including $(q,i)$ itself, where the summand is $0$; it is stated as the existence of a value $d\le-1$ to which the series converges (`HasSum`).
--
--   Differences from the source:
--   - encoding: Σ over all (q′, i′) of [Ξ(q′, i′) − Ξ(q, i)] r ≤ −1 → there is d with `HasSum` of y ↦ (Ξ(y) − Ξ(x))·Q(x, y) to d and d ≤ −1; reason: same sum, with convergence made explicit (the diagonal term is 0)
--   - encoding: n arbitrary → `[NeZero n]`; reason: μ_max and μ_min are undefined for n = 0 (no servers)
--   - encoding: servers {1, …, n} → `Fin n` (0-based); reason: Lean convention, same instances
-- source:
--   Gamarnik, Tsitsiklis, Zubeldia, Stability, Memory, and Messaging Trade-Offs in Heterogeneous Service Systems, arXiv:2007.07219v1, pp. 15–17, (A.2) and the display after (A.5)

import Mathlib
import Definitions.Def_MatrixAnalytic_Tree_Process
import Definitions.Def_StableDispatch_Markov_Setting

namespace StableDispatch.Markov

theorem drift_outside_Fn (n : ℕ) [NeZero n] (lam α : ℝ) (μ : Fin n → ℝ) (hlam0 : 0 < lam)
    (hlam1 : lam < 1) (hα : 0 < α) (hμ : μ ∈ Sigma n) :
    (Fn n lam α μ).Finite ∧
      ∀ x : State n, x ∉ Fn n lam α μ →
        ∃ d : ℝ, HasSum (fun y : State n => (Xi μ α y - Xi μ α x) * gen n lam α μ x y) d ∧
          d ≤ -1 := by sorry

end StableDispatch.Markov
