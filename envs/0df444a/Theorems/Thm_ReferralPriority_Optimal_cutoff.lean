-- Prove2me | Theorems.Thm_ReferralPriority_Optimal_cutoff
-- name    : ReferralPriority.Optimal.cutoff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:17:12.396222+00:00
-- url     : https://prove2.me/theorems/1d1c1f6c-4ee6-4f53-ac5b-759753ffa820
-- title:
--   Proof of Proposition 4, Online Appendix pp. 1–2 (PDF 34–35) — Λ∗ = µ(1 − r∗) − c/(V − r∗k) ∈ (0, µ − c/V), and (A.3) holds iff Λ ≥ Λ∗
-- statement:
--   Throughout, $\mu>0$ is the service capacity, $c>0$ the waiting cost per unit time, $V$ the value of service, $k>0$ the marginal referral cost, with Assumption 1, $V>c/\mu$; $\Lambda>0$ is the base market size.
--
--   Assume $k<V-c/\mu$, and let $r^*\in(0,1)$ be a root of the cubic $g$. Put $\Lambda^*=\mu(1-r^*)-c/(V-r^*k)$. Then
--   1. $0<\Lambda^*<\mu-c/V$;
--   2. $r^{FB}$ evaluated at $\Lambda=\Lambda^*$ equals $r^*$;
--   3. for every $0<\Lambda<\mu-c/V$, condition (A.3)
--   $$\frac{1}{\mu(1-r^{FB})-\Lambda}-\frac{k(1-r^{FB})}{c}\ \ge\ \frac{1}{\mu(1-r^{FB})-\Lambda r^{FB}}$$
--   holds if and only if $\Lambda\ge\Lambda^*$, and holds with equality if and only if $\Lambda=\Lambda^*$.
--
--   This is the step that turns the root of $g$ into the cutoff base market size separating the regimes of Proposition 4.
--
--   **Formalization Note** The positivity of $\mu$, $c$, $k$ and $\Lambda$ is added: the paper uses it throughout without stating it ($r^{FB}$ divides by $k$, and $\Lambda$ is a Poisson rate). The paper writes "(subject to $\Lambda\ge\mu-c/V$)"; the range is $\Lambda<\mu-c/V$, as stated here.
-- source:
--   Yang, Invite your friend and you'll move up in line: optimal design of referral priority programs, accepted manuscript (MSOM 23(5), 2021; eScholarship 2528d4dx), Online Appendix pp. 1–2 (PDF 34–35), proof of Proposition 4

import Mathlib
import Definitions.Def_ReferralPriority_Optimal_Model

namespace ReferralPriority.Optimal

/-- Proof of Proposition 4, Online Appendix pp. 1–2 (PDF 34–35): if k < V − c/µ and r∗ ∈ (0, 1) is a root
of g, then Λ∗ = µ(1 − r∗) − c/(V − r∗k) lies in (0, µ − c/V), r^FB at Λ∗ equals r∗, and for
0 < Λ < µ − c/V condition (A.3) holds iff Λ ≥ Λ∗, with equality in (A.3) iff Λ = Λ∗. -/
theorem cutoff (E : Env) (hS : E.Standing) (hk : E.k < E.V - E.c / E.mu) (rs : ℝ)
    (hrs : rs ∈ Set.Ioo (0 : ℝ) 1) (hg : gcubic E rs = 0) :
    0 < Lstar E rs ∧ Lstar E rs < E.mu - E.c / E.V ∧ rFB E (Lstar E rs) = rs ∧
      ∀ Lam : ℝ, 0 < Lam → Lam < E.mu - E.c / E.V →
        ((1 / (E.mu * (1 - rFB E Lam) - Lam * rFB E Lam) ≤ W1pp E Lam ↔ Lstar E rs ≤ Lam) ∧
          (1 / (E.mu * (1 - rFB E Lam) - Lam * rFB E Lam) = W1pp E Lam ↔ Lam = Lstar E rs)) := by sorry
end ReferralPriority.Optimal
