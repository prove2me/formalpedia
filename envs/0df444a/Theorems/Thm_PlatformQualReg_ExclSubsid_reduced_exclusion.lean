-- Prove2me | Theorems.Thm_PlatformQualReg_ExclSubsid_reduced_exclusion
-- name    : PlatformQualReg.ExclSubsid.reduced_exclusion
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T06:51:56.341844+00:00
-- url     : https://prove2.me/theorems/0fd335e4-1b32-4cc0-be5a-25268d622220
-- title:
--   Section 4.1, p. 12: exclusion profit in network sizes at μ = 0
-- statement:
--   Under the model's standing assumptions, every exclusion outcome satisfying both demand equations has the reduced profit
--
--   $$
--   \Pi^E=wm+\xi_1mn-\theta_cm^2-\frac{\theta_d+\lambda b}{\lambda}n^2,
--   \qquad \xi_1=\alpha_{dh}+\alpha_c+\beta q_h-\eta.
--   $$
--
--   Conversely, the paper's inverse-demand fees produce a consistent outcome for every real pair $(m,n)$. This identity supplies the objective used to find the exclusion optimum.
--
--   **Formalization Note** The paper's additional term $\mu q_hm$ vanishes because this mission fixes $\mu=0$. Consistency is stated for real network sizes; feasibility separately restricts them to nonnegative values.
-- source:
--   Huang, Lyu & Xu, Quality regulation on two-sided platforms: exclusion, subsidization, and first-party applications, SSRN 3948778, p. 12 (PDF 13), §4.1, equations (6), (8), unnumbered exclusion profit display

import Mathlib
import Definitions.Def_PlatformQualReg_ExclSubsid_Model

namespace PlatformQualReg.ExclSubsid

/-- Section 4.1, printed p. 12 (PDF 13), at μ = 0. -/
theorem reduced_exclusion (P : Params) (hP : P.Standing) :
    (∀ x : OutcomeE, ConsistentE P x →
      profitE P x = P.w * x.m + xi1 P * x.m * x.n -
        P.thc * x.m ^ 2 - (P.thd + P.lam * P.b) / P.lam * x.n ^ 2) ∧
    (∀ m n : ℝ, ConsistentE P (outE P m n)) := by sorry

end PlatformQualReg.ExclSubsid
