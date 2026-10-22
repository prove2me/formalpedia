-- Prove2me | Theorems.Thm_ReferralPriority_Optimal_first_best_achievability
-- name    : ReferralPriority.Optimal.first_best_achievability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:17:10.877101+00:00
-- url     : https://prove2.me/theorems/651b12eb-47eb-4525-b36b-cf0700d93654
-- title:
--   Proof of Proposition 4, Online Appendix p. 1 (PDF 34) — the first best is implementable iff (A.3), and only with the delays of Proposition 4 (i)
-- statement:
--   Throughout, $\mu>0$ is the service capacity, $c>0$ the waiting cost per unit time, $V$ the value of service, $k>0$ the marginal referral cost, with Assumption 1, $V>c/\mu$; $\Lambda>0$ is the base market size.
--
--   Let $0<\Lambda<\mu-c/V$. There are delays $W_1,W_0$ making $(W_1,W_0,r^{FB},1)$ feasible for Problem 1 (IC included) if and only if (A.3) holds:
--   $$\frac{1}{\mu(1-r^{FB})-\Lambda}-\frac{k(1-r^{FB})}{c}\ \ge\ \frac{1}{\mu(1-r^{FB})-\Lambda r^{FB}}.$$
--   Moreover any such delays are
--   $$W_1=\frac{1}{\mu(1-r^{FB})-\Lambda}-\frac{k(1-r^{FB})}{c},\qquad W_0=\frac{1}{\mu(1-r^{FB})-\Lambda}+\frac{kr^{FB}}{c}.$$
--
--   Together with Proposition 1 (i) this reduces achievability of the first best to the single inequality (A.3).
--
--   **Formalization Note** The positivity of $\mu$, $c$, $k$ and $\Lambda$ is added: the paper uses it throughout without stating it ($r^{FB}$ divides by $k$, and $\Lambda$ is a Poisson rate).
-- source:
--   Yang, Invite your friend and you'll move up in line: optimal design of referral priority programs, accepted manuscript (MSOM 23(5), 2021; eScholarship 2528d4dx), Online Appendix p. 1 (PDF 34), proof of Proposition 4, (A.3)

import Mathlib
import Definitions.Def_ReferralPriority_Optimal_Model

namespace ReferralPriority.Optimal

/-- Proof of Proposition 4, Online Appendix p. 1 (PDF 34): for 0 < Λ < µ − c/V, a Problem-1-feasible
tuple with (r, α) = (r^FB, 1) exists if and only if (A.3)
1/(µ(1 − r^FB) − Λ) − k(1 − r^FB)/c ≥ 1/(µ(1 − r^FB) − Λr^FB) holds, and any such tuple has the delays
W1 = 1/(µ(1 − r^FB) − Λ) − k(1 − r^FB)/c, W0 = 1/(µ(1 − r^FB) − Λ) + kr^FB/c. -/
theorem first_best_achievability (E : Env) (hS : E.Standing) (Lam : ℝ) (hL0 : 0 < Lam)
    (hL1 : Lam < E.mu - E.c / E.V) :
    ((∃ W1 W0 : ℝ, SBFeasible E Lam W1 W0 (rFB E Lam) 1) ↔
        1 / (E.mu * (1 - rFB E Lam) - Lam * rFB E Lam) ≤ W1pp E Lam) ∧
      ∀ W1 W0 : ℝ, SBFeasible E Lam W1 W0 (rFB E Lam) 1 → W1 = W1pp E Lam ∧ W0 = W0pp E Lam := by sorry
end ReferralPriority.Optimal
