-- Prove2me | Theorems.Thm_ReferralPriority_Optimal_relaxation_bound
-- name    : ReferralPriority.Optimal.relaxation_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:17:11.972422+00:00
-- url     : https://prove2.me/theorems/c304a7d2-31e4-40c4-83ef-3261ab1734bd
-- title:
--   Proof of Proposition 4, Case 2, Online Appendix p. 2 (PDF 35) — under (A.1) the throughput is at most Λ/(1 − r^SB)
-- statement:
--   Throughout, $\mu>0$ is the service capacity, $c>0$ the waiting cost per unit time, $V$ the value of service, $k>0$ the marginal referral cost, with Assumption 1, $V>c/\mu$; $\Lambda>0$ is the base market size.
--
--   Assume $k<V-c/\mu$, and let $r^{SB}=\frac{\mu(V-k)-c}{(V-k)(\mu+\Lambda)}$. Then $r^{SB}\in(0,1)$, and every $r,\alpha\in(0,1]$ with $\Lambda\alpha<\mu(1-r\alpha)$ satisfying (A.1),
--   $V-k/\alpha-c/(\mu(1-r\alpha)-\Lambda r\alpha^2)\ge0$, has
--   $$\frac{\Lambda\alpha}{1-r\alpha}\ \le\ \frac{\Lambda}{1-r^{SB}}.$$
--
--   This is the value of the relaxation problem of Case 2; combined with (A.1) it bounds the throughput of every referral-generating mechanism.
--
--   **Formalization Note** The positivity of $\mu$, $c$, $k$ and $\Lambda$ is added: the paper uses it throughout without stating it ($r^{FB}$ divides by $k$, and $\Lambda$ is a Poisson rate). The bound is stated for every $\Lambda>0$; the paper uses it for $\Lambda<\Lambda^*$.
-- source:
--   Yang, Invite your friend and you'll move up in line: optimal design of referral priority programs, accepted manuscript (MSOM 23(5), 2021; eScholarship 2528d4dx), Online Appendix p. 2 (PDF 35), proof of Proposition 4, Case 2

import Mathlib
import Definitions.Def_ReferralPriority_Optimal_Model

namespace ReferralPriority.Optimal

/-- Proof of Proposition 4, Case 2, Online Appendix p. 2 (PDF 35): if k < V − c/µ, then
r^SB = (µ(V − k) − c)/((V − k)(µ + Λ)) lies in (0, 1), and every r, α ∈ (0, 1] with Λα < µ(1 − rα) that
satisfies (A.1) has throughput Λα/(1 − rα) at most Λ/(1 − r^SB), the relaxation optimum at α = 1. -/
theorem relaxation_bound (E : Env) (hS : E.Standing) (hk : E.k < E.V - E.c / E.mu) (Lam : ℝ)
    (hL0 : 0 < Lam) :
    rSB E Lam ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ r α : ℝ, r ∈ Set.Ioc (0 : ℝ) 1 → α ∈ Set.Ioc (0 : ℝ) 1 → Stable E Lam r α →
        0 ≤ E.V - E.k / α - E.c / (E.mu * (1 - r * α) - Lam * r * α ^ 2) →
          throughput Lam r α ≤ throughput Lam (rSB E Lam) 1 := by sorry
end ReferralPriority.Optimal
