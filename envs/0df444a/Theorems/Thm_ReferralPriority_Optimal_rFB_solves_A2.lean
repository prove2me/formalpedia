-- Prove2me | Theorems.Thm_ReferralPriority_Optimal_rFB_solves_A2
-- name    : ReferralPriority.Optimal.rFB_solves_A2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:17:09.276986+00:00
-- url     : https://prove2.me/theorems/63815e6d-5385-4b15-b9f2-72326b14a034
-- title:
--   Proof of Proposition 1, Online Appendix p. 1 (PDF 34) — r^FB ∈ (0, 1) solves (A.2)
-- statement:
--   Throughout, $\mu>0$ is the service capacity, $c>0$ the waiting cost per unit time, $V$ the value of service, $k>0$ the marginal referral cost, with Assumption 1, $V>c/\mu$; $\Lambda>0$ is the base market size.
--
--   If $\Lambda<\mu-c/V$, the first-best effort
--   $$r^{FB}=\frac{-\sqrt{4k\mu(c+\Lambda V-\mu V)+(-k\Lambda+k\mu+\mu V)^2}-k\Lambda+k\mu+\mu V}{2k\mu}$$
--   satisfies $0<r^{FB}<1$, $\mu(1-r^{FB})-\Lambda>0$, and solves (A.2):
--   $$V-r^{FB}k-\frac{c}{\mu(1-r^{FB})-\Lambda}=0.$$
--
--   This identifies the closed form of Proposition 1 with the root of the binding IR condition at $\alpha=1$ and is used throughout the proof of Proposition 4.
--
--   **Formalization Note** The positivity of $\mu$, $c$, $k$ and $\Lambda$ is added: the paper uses it throughout without stating it ($r^{FB}$ divides by $k$, and $\Lambda$ is a Poisson rate).
-- source:
--   Yang, Invite your friend and you'll move up in line: optimal design of referral priority programs, accepted manuscript (MSOM 23(5), 2021; eScholarship 2528d4dx), Online Appendix p. 1 (PDF 34), proof of Proposition 1 and proof of Proposition 4, (A.2)

import Mathlib
import Definitions.Def_ReferralPriority_Optimal_Model

namespace ReferralPriority.Optimal

/-- Proof of Proposition 1 and of Proposition 4, Online Appendix p. 1 (PDF 34): for 0 < Λ < µ − c/V,
r^FB lies in (0, 1), the queue at (r^FB, α = 1) is stable, and r^FB solves (A.2):
V − r^FB k − c/(µ(1 − r^FB) − Λ) = 0. -/
theorem rFB_solves_A2 (E : Env) (hS : E.Standing) (Lam : ℝ) (hL0 : 0 < Lam)
    (hL1 : Lam < E.mu - E.c / E.V) :
    0 < rFB E Lam ∧ rFB E Lam < 1 ∧ 0 < E.mu * (1 - rFB E Lam) - Lam ∧
      E.V - rFB E Lam * E.k - E.c / (E.mu * (1 - rFB E Lam) - Lam) = 0 := by sorry
end ReferralPriority.Optimal
