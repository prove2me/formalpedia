-- Prove2me | Theorems.Thm_ReferralPriority_Optimal_eq_A1
-- name    : ReferralPriority.Optimal.eq_A1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:17:10.037797+00:00
-- url     : https://prove2.me/theorems/80a5f027-3be4-476f-8ec3-a5549690fd7c
-- title:
--   Proof of Proposition 3, Online Appendix p. 1 (PDF 34) — (A.1): every referral-generating mechanism has V − k/α − c/(µ(1 − rα) − Λrα²) ≥ 0
-- statement:
--   Throughout, $\mu>0$ is the service capacity, $c>0$ the waiting cost per unit time, $V$ the value of service, $k>0$ the marginal referral cost, with Assumption 1, $V>c/\mu$; $\Lambda>0$ is the base market size.
--
--   Let $(W_1,W_0,r,\alpha)$ be feasible for Problem 1 with $r>0$ and $\alpha>0$, i.e. a mechanism that generates referrals. Then
--   $$V-\frac{k}{\alpha}-\frac{c}{\mu(1-r\alpha)-\Lambda r\alpha^2}\ \ge 0.\qquad\text{(A.1)}$$
--
--   (A.1) is the constraint of the one-dimensional relaxation used to bound the second-best throughput in Proposition 4 (iii).
--
--   **Formalization Note** The positivity of $\mu$, $c$, $k$ and $\Lambda$ is added: the paper uses it throughout without stating it ($r^{FB}$ divides by $k$, and $\Lambda$ is a Poisson rate).
-- source:
--   Yang, Invite your friend and you'll move up in line: optimal design of referral priority programs, accepted manuscript (MSOM 23(5), 2021; eScholarship 2528d4dx), Online Appendix p. 1 (PDF 34), proof of Proposition 3, (A.1)

import Mathlib
import Definitions.Def_ReferralPriority_Optimal_Model

namespace ReferralPriority.Optimal

/-- Proof of Proposition 3, Online Appendix p. 1 (PDF 34), (A.1): every Problem-1-feasible tuple that
generates referrals (r > 0, α > 0) satisfies V − k/α − c/(µ(1 − rα) − Λrα²) ≥ 0. -/
theorem eq_A1 (E : Env) (hS : E.Standing) (Lam : ℝ) (hL0 : 0 < Lam) (W1 W0 r α : ℝ)
    (h : SBFeasible E Lam W1 W0 r α) (hr : 0 < r) (hα : 0 < α) :
    0 ≤ E.V - E.k / α - E.c / (E.mu * (1 - r * α) - Lam * r * α ^ 2) := by sorry
end ReferralPriority.Optimal
