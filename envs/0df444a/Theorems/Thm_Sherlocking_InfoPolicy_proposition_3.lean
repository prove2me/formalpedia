-- Prove2me | Theorems.Thm_Sherlocking_InfoPolicy_proposition_3
-- name    : Sherlocking.InfoPolicy.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:26:23.422548+00:00
-- url     : https://prove2.me/theorems/0b581587-7ca6-4b0b-812c-a071c60821d8
-- title:
--   Proposition 3, p. 15 (PDF 17) — the full commitment outcome at r^C is implementable by an information policy iff (OC0) holds at r^C, equivalently (4)
-- statement:
--   Let $\delta<1$ and $K$ satisfy Assumption 1, $1-\delta<K<\delta$. Let $r^C\in[0,1]$ be a solution of the full-commitment problem
--   $$\mathcal P_C:\quad \max_{r\in[0,1]}\Pi^C_P(r),\qquad \Pi^C_P(r) = \int_{\theta_S(r)}^{\theta_P(r)} r\theta\,d\theta + \int_{\theta_P(r)}^{1}\Big[(1-\delta)r\theta + \alpha(\theta;r)(\delta\theta-K) + (1-\alpha(\theta;r))\delta r\theta\Big]d\theta .$$
--   Then
--
--   1. the full commitment outcome at fee $r^C$ is implementable by an information policy (there exist a set of realizations $X$, a measurable signal $\sigma$, a platform strategy and an entry set forming a weak perfect Bayesian equilibrium whose outcome is the full commitment outcome) if and only if (OC0) holds at $r=r^C$;
--   2. (OC0) at $r^C$ is equivalent to
--   $$\int_{\theta_P(r^C)}^{1}(\theta-\theta_P(r^C))\,(1-\alpha(\theta;r^C))\,d\theta\ \le\ \int_{\theta_S(r^C)}^{\theta_P(r^C)}(\theta_P(r^C)-\theta)\,d\theta. \tag{4}$$
--
--   This is the paper's characterization of when the platform's control of its own information can replace commitment to its entry policy.
--
--   **Formalization Note** $r^C$ is any maximizer of $\Pi^C_P$ on $[0,1]$; the printed statement presumes the solution is unique, and the formal statement holds for every maximizer. $\delta<1$ is added (the period lengths are $1-\delta$ and $\delta$). No hypothesis $r^C<1-K$ is assumed: it follows from maximality, since $\Pi^C_P$ vanishes for $r\ge1-K$ and is positive for small $r>0$. Implementability quantifies over every realization space `X : Type`, every measurable signal and strategy, and the full equilibrium predicate of the model; it is not defined through (OC0).
-- source:
--   Choi, Kim & Mukherjee, “Sherlocking” and Platform Information Policy, CESifo Working Paper No. 10769 / SSRN 4643950 (version of November 13, 2023), p. 15 (PDF 17), Proposition 3, Eq. (4)

import Mathlib
import Definitions.Def_Sherlocking_InfoPolicy_Model

namespace Sherlocking.InfoPolicy

theorem proposition_3 (K δ rC : ℝ) (hδ1 : δ < 1) (hK1 : 1 - δ < K) (hK2 : K < δ) (hrC : rC ∈ Set.Icc (0:ℝ) 1) (hmax : IsMaxOn (PiC K δ) (Set.Icc (0:ℝ) 1) rC) : (CommitmentImplementable K δ rC ↔ OC0 K δ rC) ∧ (OC0 K δ rC ↔ Ineq4 K δ rC) := by sorry

end Sherlocking.InfoPolicy
