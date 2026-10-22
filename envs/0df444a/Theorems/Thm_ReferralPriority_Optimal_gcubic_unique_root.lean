-- Prove2me | Theorems.Thm_ReferralPriority_Optimal_gcubic_unique_root
-- name    : ReferralPriority.Optimal.gcubic_unique_root
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:17:19.610568+00:00
-- url     : https://prove2.me/theorems/66dbf035-8a4b-4b4b-8558-a8d1a5bf68fb
-- title:
--   Proof of Proposition 4, Online Appendix p. 2 (PDF 35) — if k < V − c/µ, the cubic g has a unique root r∗ in (0, 1), positive before it and negative after
-- statement:
--   Throughout, $\mu>0$ is the service capacity, $c>0$ the waiting cost per unit time, $V$ the value of service, $k>0$ the marginal referral cost, with Assumption 1, $V>c/\mu$; $\Lambda>0$ is the base market size.
--
--   Let $g(r)=(\mu(1-r)^2(V-rk)+rc)(V-k)-c(V-rk)$. If $k<V-c/\mu$, there is $r^*\in(0,1)$ with $g(r^*)=0$ such that $r^*$ is the only root of $g$ in $(0,1)$, and
--   $$g(r)>0\ \text{ for } r\in(0,r^*),\qquad g(r)<0\ \text{ for } r\in(r^*,1).$$
--
--   The root $r^*$ determines the cutoff $\Lambda^*=\mu(1-r^*)-c/(V-r^*k)$ of Proposition 4.
--
--   **Formalization Note** The positivity of $\mu$, $c$, $k$ and $\Lambda$ is added: the paper uses it throughout without stating it ($r^{FB}$ divides by $k$, and $\Lambda$ is a Poisson rate).
-- source:
--   Yang, Invite your friend and you'll move up in line: optimal design of referral priority programs, accepted manuscript (MSOM 23(5), 2021; eScholarship 2528d4dx), Online Appendix p. 2 (PDF 35), proof of Proposition 4 (the cubic g)

import Mathlib
import Definitions.Def_ReferralPriority_Optimal_Model

namespace ReferralPriority.Optimal

/-- Proof of Proposition 4, Online Appendix p. 2 (PDF 35): if k < V − c/µ, the cubic
g(r) = (µ(1 − r)²(V − rk) + rc)(V − k) − c(V − rk) has a unique root r∗ in (0, 1); g > 0 on (0, r∗)
and g < 0 on (r∗, 1). -/
theorem gcubic_unique_root (E : Env) (hS : E.Standing) (hk : E.k < E.V - E.c / E.mu) :
    ∃ rs ∈ Set.Ioo (0 : ℝ) 1, gcubic E rs = 0 ∧
      (∀ r ∈ Set.Ioo (0 : ℝ) 1, gcubic E r = 0 → r = rs) ∧
      (∀ r ∈ Set.Ioo 0 rs, 0 < gcubic E r) ∧
      (∀ r ∈ Set.Ioo rs 1, gcubic E r < 0) := by sorry
end ReferralPriority.Optimal
