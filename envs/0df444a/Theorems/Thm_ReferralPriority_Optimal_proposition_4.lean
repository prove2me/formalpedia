-- Prove2me | Theorems.Thm_ReferralPriority_Optimal_proposition_4
-- name    : ReferralPriority.Optimal.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:17:25.706118+00:00
-- url     : https://prove2.me/theorems/bcdaa7e7-8745-4911-a59c-aa3f7109e2f0
-- title:
--   Proposition 4, p. 15 (PDF 16) — if k < V − c/µ, a unique Λ∗ separates partial priority (first best), full priority (first best) and strategic delay (second-best optimal)
-- statement:
--   Throughout, $\mu>0$ is the service capacity, $c>0$ the waiting cost per unit time, $V$ the value of service, $k>0$ the marginal referral cost, with Assumption 1, $V>c/\mu$; $\Lambda>0$ is the base market size.
--
--   If $k<V-c/\mu$, there is a unique $\Lambda^*\in(0,\mu-c/V)$ such that for every $0<\Lambda<\mu-c/V$:
--   1. if $\Lambda>\Lambda^*$, the first best is achieved by partial priority with $\alpha=1$, $r=r^{FB}$ and
--   $$W_1=\frac{1}{\mu(1-r^{FB})-\Lambda}-\frac{k(1-r^{FB})}{c},\qquad W_0=\frac{1}{\mu(1-r^{FB})-\Lambda}+\frac{kr^{FB}}{c};$$
--   2. if $\Lambda=\Lambda^*$, the first best is achieved by full priority (with the same $\alpha$, $r$, $W_1$, $W_0$);
--   3. if $\Lambda<\Lambda^*$, the first best cannot be achieved by any mechanism feasible for Problem 1, and strategic delay is optimal in the second best, with
--   $$\alpha^{SB}=1,\quad r^{SB}=\frac{\mu(V-k)-c}{(V-k)(\mu+\Lambda)},\quad W_1=\frac{1}{\mu(1-r^{SB})-\Lambda r^{SB}},\quad W_0=W_1+\frac{k}{c};$$
--   at this tuple (6a) is slack and (6b) binds.
--
--   Here "the first best is achieved" means: the tuple is feasible for Problem 1 (IR, IC, OA, stability) and its throughput equals the maximum of the first-best problem (Problem 1 without IC). "Optimal in the second best" means its throughput is the maximum over all Problem-1-feasible tuples. The result is the paper's main characterization of the optimal referral priority program.
--
--   **Formalization Note** The positivity of $\mu$, $c$, $k$ and $\Lambda$ is added: the paper uses it throughout without stating it ($r^{FB}$ divides by $k$, and $\Lambda$ is a Poisson rate). $\Lambda^*$ is chosen before $\Lambda$, so it depends only on $(\mu,c,V,k)$. Part (ii) names no delays on the page; the delays of part (i) are used, and they are the only ones that can achieve the first best at $r^{FB}$. The page's description of the strategic-delay tuple ("(6a) is non-binding but (6b) is binding", p. 16) is included in (iii).
-- source:
--   Yang, Invite your friend and you'll move up in line: optimal design of referral priority programs, accepted manuscript (MSOM 23(5), 2021; eScholarship 2528d4dx), p. 15 (PDF 16), Proposition 4; p. 16 (PDF 17)

import Mathlib
import Definitions.Def_ReferralPriority_Optimal_Model

namespace ReferralPriority.Optimal

/-- Proposition 4, p. 15 (PDF 16): if k < V − c/µ, there is a unique cutoff Λ∗ ∈ (0, µ − c/V) such that,
for 0 < Λ < µ − c/V,
(i) if Λ > Λ∗, the first best is achieved by partial priority with W1 = 1/(µ(1 − r^FB) − Λ) − k(1 − r^FB)/c,
W0 = 1/(µ(1 − r^FB) − Λ) + kr^FB/c (and α = 1, r = r^FB);
(ii) if Λ = Λ∗, the first best is achieved by full priority (with the same delays);
(iii) if Λ < Λ∗, the first best cannot be achieved, and strategic delay with α^SB = 1,
r^SB = (µ(V − k) − c)/((V − k)(µ + Λ)), W1 = 1/(µ(1 − r^SB) − Λr^SB), W0 = W1 + k/c is optimal in the
second best ((6a) slack, (6b) binding). -/
theorem proposition_4 (E : Env) (hS : E.Standing) (hk : E.k < E.V - E.c / E.mu) :
    ∃! Ls : ℝ, 0 < Ls ∧ Ls < E.mu - E.c / E.V ∧
      ∀ Lam : ℝ, 0 < Lam → Lam < E.mu - E.c / E.V →
        (Ls < Lam →
            AchievesFB E Lam (W1pp E Lam) (W0pp E Lam) (rFB E Lam) 1 ∧
            PartialPriority E Lam (W1pp E Lam) (W0pp E Lam) (rFB E Lam) 1) ∧
        (Lam = Ls →
            AchievesFB E Lam (W1pp E Lam) (W0pp E Lam) (rFB E Lam) 1 ∧
            FullPriority E Lam (W1pp E Lam) (W0pp E Lam) (rFB E Lam) 1) ∧
        (Lam < Ls →
            ¬ FBAchievable E Lam ∧
            SBOptimal E Lam (W1sd E Lam) (W0sd E Lam) (rSB E Lam) 1 ∧
            StrategicDelay E Lam (W1sd E Lam) (W0sd E Lam) (rSB E Lam) 1 ∧
            OA6bBinding E Lam (W1sd E Lam) (rSB E Lam) 1) := by sorry
end ReferralPriority.Optimal
