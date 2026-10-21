-- Prove2me | Theorems.Thm_PandemicInfo_Inequality_theorem_1
-- name    : PandemicInfo.Inequality.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:34:20.416255+00:00
-- url     : https://prove2.me/theorems/57d37b65-a288-4390-8e41-6d62e19bd20c
-- title:
--   Theorem 1, pp. 9–10 (PDF 10–11) — optimal policy: no disclosure, full disclosure, exaggerate or downplay by $\lambda_1$–$\lambda_4$, $\mu^{EX}_\lambda$, $\mu^{DP}_\lambda$
-- statement:
--   **Theorem 1 (optimal information policy).** Fix the model of §2 and a weight $\lambda\in[0,1]$. The thresholds satisfy $\lambda_1\le\lambda_2\le1/2\le\lambda_3\le\lambda_4$, and
--
--   1. if $\lambda\le\lambda_1$ or $\lambda\ge\lambda_4$, no disclosure is optimal;
--   2. if $\lambda_2\le\lambda\le\lambda_3$, full disclosure is optimal;
--   3. if $\lambda_1<\lambda<\lambda_2$: when $\mu^\circ<\mu^{EX}_\lambda$ some exaggerating binary policy ($\pi(m_h\mid\omega_h)=1$, $\pi(m_h\mid\omega_\ell)>0$) is optimal, and otherwise no disclosure is optimal;
--   4. if $\lambda_3<\lambda<\lambda_4$: when $\mu^\circ>\mu^{DP}_\lambda$ some downplaying binary policy ($\pi(m_\ell\mid\omega_\ell)=1$, $\pi(m_\ell\mid\omega_h)>0$) is optimal, and otherwise no disclosure is optimal.
--
--   Optimality is for the government's problem (6): the policy, together with some Bayesian Nash equilibrium profile, minimizes $C_\lambda$ over all finite-message policies and all their BNE profiles.
--
--   **Formalization Note** "No disclosure is optimal" is stated for every binary no-disclosure policy ($\pi(m_\ell\mid\omega_\ell)=p=\pi(m_\ell\mid\omega_h)$, any $p\in[0,1]$), all of which induce the single posterior $\mu^\circ$. The paper says the policy "solves (12)"; (12) is (6) rewritten through Proposition 1, and the Lean states optimality for (6). The thresholds are the sentinel forms of the definition file. The "Furthermore" sentence of the theorem (monotonicity in $\kappa$, values at the cutoffs) is word for word Lemma 2 and is formalized there. All statements assume the standing assumptions of §2 (`Params.Standing`), which include the theorem's $\sigma>0$ and $\kappa>0$.
-- source:
--   de Véricourt, Gurkan, Wang, Informing the Public about a Pandemic, ESMT Working Paper 20-03 (Dec. 15, 2020), pp. 9–10 (PDF 10–11), Theorem 1

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope
import Definitions.Def_PandemicInfo_Inequality_Model
import Definitions.Def_PandemicInfo_Inequality_Reduced

namespace PandemicInfo.Inequality

/-- Theorem 1, pp. 9–10: the optimal information policy of (6) by regime of `λ`. The binary
policies: no disclosure `binPolicy p (1 - p)`, full disclosure `binPolicy 1 1`, exaggerating
`binPolicy pl 1` with `π(m_h | ω_ℓ) = 1 - pl > 0`, downplaying `binPolicy 1 ph` with
`π(m_ℓ | ω_h) = 1 - ph > 0`. -/
theorem theorem_1 (P : Params) (hS : P.Standing) (lam : ℝ) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) :
    (P.lam1 ≤ P.lam2 ∧ P.lam2 ≤ 1 / 2 ∧ 1 / 2 ≤ P.lam3 ∧ P.lam3 ≤ P.lam4) ∧
    ((lam ≤ P.lam1 ∨ P.lam4 ≤ lam) →
      ∀ p : ℝ, 0 ≤ p → p ≤ 1 → P.IsOptimalPolicy lam (binPolicy p (1 - p))) ∧
    ((P.lam2 ≤ lam ∧ lam ≤ P.lam3) → P.IsOptimalPolicy lam (binPolicy 1 1)) ∧
    ((P.lam1 < lam ∧ lam < P.lam2) →
      (P.μ0 < P.μEX lam →
        ∃ pl : ℝ, 0 ≤ pl ∧ pl < 1 ∧ P.IsOptimalPolicy lam (binPolicy pl 1)) ∧
      (P.μEX lam ≤ P.μ0 →
        ∀ p : ℝ, 0 ≤ p → p ≤ 1 → P.IsOptimalPolicy lam (binPolicy p (1 - p)))) ∧
    ((P.lam3 < lam ∧ lam < P.lam4) →
      (P.μDP lam < P.μ0 →
        ∃ ph : ℝ, 0 ≤ ph ∧ ph < 1 ∧ P.IsOptimalPolicy lam (binPolicy 1 ph)) ∧
      (P.μ0 ≤ P.μDP lam →
        ∀ p : ℝ, 0 ≤ p → p ≤ 1 → P.IsOptimalPolicy lam (binPolicy p (1 - p)))) := by sorry

end PandemicInfo.Inequality
