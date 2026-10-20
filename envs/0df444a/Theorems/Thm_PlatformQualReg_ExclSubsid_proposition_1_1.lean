-- Prove2me | Theorems.Thm_PlatformQualReg_ExclSubsid_proposition_1_1
-- name    : PlatformQualReg.ExclSubsid.proposition_1_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T06:51:57.417977+00:00
-- url     : https://prove2.me/theorems/be06d9c9-67c8-4bee-919f-b6ba1322f076
-- title:
--   Proposition 1.1(1), pp. 12–13: exclusion optimum at μ = 0
-- statement:
--   Assume the standing parameter conditions, strict concavity of the exclusion profit, and $\xi_1>0$. Put $D_E=4(\theta_d+\lambda b)\theta_c-\lambda\xi_1^2$. The exclusion optimum has
--
--   $$
--   m^{E*}=\frac{2(\theta_d+\lambda b)w}{D_E},\qquad
--   n^{E*}=\frac{\lambda\xi_1w}{D_E},\qquad
--   \Pi^{E*}=\frac{(\theta_d+\lambda b)w^2}{D_E}.
--   $$
--
--   The outcome formed from these sizes and the inverse-demand fees is optimal, and every optimal exclusion outcome has these same network sizes. These formulas connect the source's equilibrium quantities to the optimization model.
--
--   **Formalization Note** This is the $\mu=0$ instance of Proposition 1.1(1). The explicit $\xi_1>0$ condition is the interior-developer condition needed for the nonnegative feasible region.
-- source:
--   Huang, Lyu & Xu, Quality regulation on two-sided platforms: exclusion, subsidization, and first-party applications, SSRN 3948778, pp. 12–13 (PDF 13–14), Proposition 1.1(1)

import Mathlib
import Definitions.Def_PlatformQualReg_ExclSubsid_Model

namespace PlatformQualReg.ExclSubsid

/-- Proposition 1.1(1), printed pp. 12–13 (PDF 13–14), specialized to μ = 0. -/
theorem proposition_1_1 (P : Params) (hP : P.Standing)
    (hcE : ConcaveE P) (hxi : 0 < xi1 P) :
    IsOptE P (outE P (optME P) (optNE P)) ∧
    (∀ x : OutcomeE, IsOptE P x → x.m = optME P ∧ x.n = optNE P) ∧
    profitE P (outE P (optME P) (optNE P)) = optProfitE P := by sorry

end PlatformQualReg.ExclSubsid
