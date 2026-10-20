-- Prove2me | Theorems.Thm_PlatformQualReg_ExclSubsid_proposition_2_2
-- name    : PlatformQualReg.ExclSubsid.proposition_2_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T06:52:16.870162+00:00
-- url     : https://prove2.me/theorems/bf03c6a6-741e-4086-9003-f93f2ebbeeaa
-- title:
--   Proposition 2.2(1), p. 17: optimal subsidy at μ = 0
-- statement:
--   Assume the standing parameter conditions, strict concavity of the subsidy problem, and $\alpha_{dh}-\alpha_{dl}\le\beta q_h$. For an optimal interior subsidy outcome, write $D_S=4(\theta_d+b)\theta_c-\xi^2-\tau$. Then
--
--   $$
--   \gamma^*=\frac{(\theta_d+b)w[\beta q_h-(\alpha_{dh}-\alpha_{dl})]}{D_S},\quad
--   m^{S*}=\frac{2(\theta_d+b)w}{D_S},\quad
--   n^{S*}=\frac{\xi w}{D_S},\quad
--   \Pi^{S*}=\frac{(\theta_d+b)w^2}{D_S}.
--   $$
--
--   The formula for $\gamma^*$ is Proposition 2.2(1). The companion size and profit identities locate the same optimum in the model and support the strategy comparison.
--
--   **Formalization Note** The paper prints only $\gamma^*$ here; the three companion identities are derived from its reduced profit objective because Appendix 1, which contains its closed forms, is absent from the held PDF. The inequality on $\alpha_{dh}-\alpha_{dl}$ selects the nonnegative-subsidy regime; equality allows the boundary case $\gamma^*=0$. Interior means positive consumers and positive developer counts of both types.
-- source:
--   Huang, Lyu & Xu, Quality regulation on two-sided platforms: exclusion, subsidization, and first-party applications, SSRN 3948778, p. 17 (PDF 18), Proposition 2.2(1), with size and profit identities derived from §4.2 p. 16 (PDF 17) reduced objective

import Mathlib
import Definitions.Def_PlatformQualReg_ExclSubsid_Model

namespace PlatformQualReg.ExclSubsid

/-- Proposition 2.2(1), printed p. 17 (PDF 18), at μ = 0; sizes and profit are derived. -/
theorem proposition_2_2 (P : Params) (hP : P.Standing)
    (hcS : ConcaveS P) (hsub : P.adh - P.adl ≤ P.β * P.qh)
    (x : OutcomeS) (hx : IsOptS P x)
    (hint : 0 < x.m ∧ 0 < nl P x ∧ 0 < nh P x) :
    x.γ = optGammaS P ∧ x.m = optMS P ∧ x.n = optNS P ∧
    profitS P x = optProfitS P := by sorry

end PlatformQualReg.ExclSubsid
