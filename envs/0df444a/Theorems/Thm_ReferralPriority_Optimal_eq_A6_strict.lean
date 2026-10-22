-- Prove2me | Theorems.Thm_ReferralPriority_Optimal_eq_A6_strict
-- name    : ReferralPriority.Optimal.eq_A6_strict
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:17:14.614138+00:00
-- url     : https://prove2.me/theorems/64745d2b-7c0c-4ea9-b216-4d69c7381379
-- title:
--   Proof of Proposition 4, Online Appendix p. 3 (PDF 36) — (A.6) holds strictly for Λ < Λ∗
-- statement:
--   Throughout, $\mu>0$ is the service capacity, $c>0$ the waiting cost per unit time, $V$ the value of service, $k>0$ the marginal referral cost, with Assumption 1, $V>c/\mu$; $\Lambda>0$ is the base market size.
--
--   Assume $k<V-c/\mu$, let $r^*\in(0,1)$ be a root of $g$, $\Lambda^*=\mu(1-r^*)-c/(V-r^*k)$, and $0<\Lambda<\Lambda^*$. With $r^{SB}=\frac{\mu(V-k)-c}{(V-k)(\mu+\Lambda)}$,
--   $$\mu(1-r^{SB})-\Lambda>0\qquad\text{and}\qquad V-r^{SB}k-\frac{c}{\mu(1-r^{SB})-\Lambda}>0.\qquad\text{(A.6)}$$
--
--   Strictness of (A.6) is what makes the relaxation optimum implementable with (6a) slack, i.e. by strategic delay.
--
--   **Formalization Note** The positivity of $\mu$, $c$, $k$ and $\Lambda$ is added: the paper uses it throughout without stating it ($r^{FB}$ divides by $k$, and $\Lambda$ is a Poisson rate). The positivity of $\mu(1-r^{SB})-\Lambda$ is argued circularly on the page; it is stated here as part of the claim.
-- source:
--   Yang, Invite your friend and you'll move up in line: optimal design of referral priority programs, accepted manuscript (MSOM 23(5), 2021; eScholarship 2528d4dx), Online Appendix p. 3 (PDF 36), proof of Proposition 4, (A.6)

import Mathlib
import Definitions.Def_ReferralPriority_Optimal_Model

namespace ReferralPriority.Optimal

/-- Proof of Proposition 4, Online Appendix p. 3 (PDF 36), (A.6) strictly: if k < V − c/µ, r∗ ∈ (0, 1) is a
root of g and 0 < Λ < Λ∗ = µ(1 − r∗) − c/(V − r∗k), then µ(1 − r^SB) − Λ > 0 and
V − r^SB k − c/(µ(1 − r^SB) − Λ) > 0. -/
theorem eq_A6_strict (E : Env) (hS : E.Standing) (hk : E.k < E.V - E.c / E.mu) (rs : ℝ)
    (hrs : rs ∈ Set.Ioo (0 : ℝ) 1) (hg : gcubic E rs = 0) (Lam : ℝ) (hL0 : 0 < Lam)
    (hL : Lam < Lstar E rs) :
    0 < E.mu * (1 - rSB E Lam) - Lam ∧
      0 < E.V - rSB E Lam * E.k - E.c / (E.mu * (1 - rSB E Lam) - Lam) := by sorry
end ReferralPriority.Optimal
