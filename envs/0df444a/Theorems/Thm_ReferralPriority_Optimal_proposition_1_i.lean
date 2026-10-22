-- Prove2me | Theorems.Thm_ReferralPriority_Optimal_proposition_1_i
-- name    : ReferralPriority.Optimal.proposition_1_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:17:03.817832+00:00
-- url     : https://prove2.me/theorems/621f1f6f-50ad-4d3d-b731-278bf901c230
-- title:
--   Proposition 1 (i), p. 12 (PDF 13) — for Λ < µ − c/V the first best is α = 1, r = r^FB > 0, and every first-best optimum is work-conserving
-- statement:
--   Throughout, $\mu>0$ is the service capacity, $c>0$ the waiting cost per unit time, $V$ the value of service, $k>0$ the marginal referral cost, with Assumption 1, $V>c/\mu$; $\Lambda>0$ is the base market size.
--
--   Consider the first-best problem: maximize the throughput $\Lambda\alpha/(1-r\alpha)$ over $W_1,W_0\ge 0$, $r,\alpha\in[0,1]$ subject to IR (4), the OA constraints (6a)–(6c) and stability (7), but not IC (5). If $\Lambda<\mu-c/V$, then $r^{FB}>0$,
--   $$\frac{\Lambda}{1-r^{FB}}=\max\Big\{\frac{\Lambda\alpha}{1-r\alpha}: (W_1,W_0,r,\alpha)\ \text{first-best feasible}\Big\},$$
--   the maximum being attained at $\alpha=1$, $r=r^{FB}$; and every first-best-feasible tuple attaining it has $\alpha^{FB}=1$, $r=r^{FB}$ and is work-conserving: $r\alpha W_1+(1-r\alpha)W_0=1/(\mu(1-r\alpha)-\Lambda\alpha)$.
--
--   This is the benchmark against which Proposition 4 measures the second best.
--
--   **Formalization Note** The positivity of $\mu$, $c$, $k$ and $\Lambda$ is added: the paper uses it throughout without stating it ($r^{FB}$ divides by $k$, and $\Lambda$ is a Poisson rate). "The first-best problem solution is always work-conserving" is read as: every optimal tuple satisfies (6a) with equality. Part (ii), $\Lambda\ge\mu-c/V$, is not formalized.
-- source:
--   Yang, Invite your friend and you'll move up in line: optimal design of referral priority programs, accepted manuscript (MSOM 23(5), 2021; eScholarship 2528d4dx), p. 12 (PDF 13), Proposition 1 (i); p. 13 (PDF 14)

import Mathlib
import Definitions.Def_ReferralPriority_Optimal_Model

namespace ReferralPriority.Optimal

/-- Proposition 1 (i), p. 12 (PDF 13): if 0 < Λ < µ − c/V, then in the first-best problem (Problem 1
without IC) the throughput of (α, r) = (1, r^FB) is the maximum, r^FB > 0, and every first-best-feasible
tuple attaining the maximum has α = 1, r = r^FB and is work-conserving ((6a) binding). -/
theorem proposition_1_i (E : Env) (hS : E.Standing) (Lam : ℝ) (hL0 : 0 < Lam)
    (hL1 : Lam < E.mu - E.c / E.V) :
    0 < rFB E Lam ∧
      IsGreatest (FBValues E Lam) (throughput Lam (rFB E Lam) 1) ∧
      ∀ W1 W0 r α : ℝ, FBFeasible E Lam W1 W0 r α →
        throughput Lam r α = throughput Lam (rFB E Lam) 1 →
          α = 1 ∧ r = rFB E Lam ∧ WorkConserving E Lam W1 W0 r α := by sorry
end ReferralPriority.Optimal
