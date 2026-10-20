-- Prove2me | Theorems.Thm_PlatformQualReg_ExclSubsid_reduced_subsidization
-- name    : PlatformQualReg.ExclSubsid.reduced_subsidization
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T06:52:04.392413+00:00
-- url     : https://prove2.me/theorems/a36132ac-6c49-4b92-83f4-1f840ab88987
-- title:
--   Section 4.2, pp. 15–16: subsidy profit in network sizes at μ = 0
-- statement:
--   Under the standing assumptions, every subsidization outcome satisfying the demand equations has high-quality developer count $n_h=\lambda n+\rho m+t\gamma$ and reduced profit
--
--   $$
--   \Pi^S=wm+\xi mn-\theta_cm^2-(\theta_d+b)n^2
--     +\beta m(\rho q_hm+\gamma tq_h)-\gamma\rho m
--     -\frac{\lambda(1-\lambda)}{\theta_d}\gamma^2.
--   $$
--
--   The inverse-demand fees produce a consistent outcome for every real triple $(m,n,\gamma)$. This identity supplies the subsidy objective and keeps the quality gain and subsidy cost explicit.
--
--   **Formalization Note** The paper's terms involving $\mu$ vanish at $\mu=0$. Feasibility, rather than consistency, imposes nonnegative counts and subsidy.
-- source:
--   Huang, Lyu & Xu, Quality regulation on two-sided platforms: exclusion, subsidization, and first-party applications, SSRN 3948778, pp. 15–16 (PDF 16–17), §4.2, equations (10), (11), (13), unnumbered subsidization profit display

import Mathlib
import Definitions.Def_PlatformQualReg_ExclSubsid_Model

namespace PlatformQualReg.ExclSubsid

/-- Section 4.2, printed pp. 15–16 (PDF 16–17), at μ = 0. -/
theorem reduced_subsidization (P : Params) (hP : P.Standing) :
    (∀ x : OutcomeS, ConsistentS P x →
      nh P x = P.lam * x.n + rho P * x.m + t P * x.γ ∧
      profitS P x = P.w * x.m + xi P * x.m * x.n -
        P.thc * x.m ^ 2 - (P.thd + P.b) * x.n ^ 2 +
        x.m * (rho P * P.qh * x.m + x.γ * t P * P.qh) * P.β -
        x.γ * rho P * x.m - x.γ ^ 2 * P.lam * (1 - P.lam) / P.thd) ∧
    (∀ m n γ : ℝ, ConsistentS P (outS P m n γ)) := by sorry

end PlatformQualReg.ExclSubsid
