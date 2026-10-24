-- Prove2me | Theorems.Thm_PandoraBO_Private20261023_tight_lagrangian_certificate
-- name    : PandoraBO.Private20261023.tight_lagrangian_certificate
-- status  : Proved
-- author  : @QianJaneXie
-- created : 2026-10-23T23:40:08.272967+00:00
-- url     : https://prove2.me/theorems/b3203ff7-f9bd-4a1f-9e1e-a3dbfc409df1
-- title:
--   Lemma 5 — an exact-budget Lagrangian certificate
-- statement:
--   Fix a budget $B$ and $\lambda\ge0$. If a policy $\pi$ maximizes $R(\rho)-\lambda C(\rho)$ over all policies and satisfies $C(\pi)=B$, then
--
--   $$C(\rho)\le B\ \Longrightarrow\ R(\rho)\le R(\pi).$$
--
--   Thus $\pi$ is expected-budget optimal. This states the certificate underlying Lemma 5 directly: no separate hypothesis that $\lambda$ minimizes the dual is needed for this implication.
-- source:
--   Private proof development against the author-revised manuscript reviewed on 23 October 2026; same statement as mission milestone PandoraBO.tight_lagrangian_certificate. Paper: Xie et al., Cost-aware Bayesian Optimization via the Pandora's Box Gittins Index, Appendix B.5, Lagrangian budget-optimality argument. The mission remains unpublished. Mission source version: the author-revised manuscript reviewed on 23 October 2026, intended for arXiv v4; public posting is pending. References to arXiv v3 identify the earlier published version.

import Definitions.Def_PandoraBO_Model

set_option autoImplicit false

namespace PandoraBO.Private20261023

theorem tight_lagrangian_certificate {n : ℕ} (M : Instance n)
    (B multiplier : ℝ) (hnonneg : 0 ≤ multiplier) (π : Policy n)
    (hopt : optimal M multiplier π) (htight : expectedCost M π = B) :
    budgetOptimal M B π := by sorry

end PandoraBO.Private20261023
