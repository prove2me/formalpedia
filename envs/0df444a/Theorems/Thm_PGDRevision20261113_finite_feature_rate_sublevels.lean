-- Prove2me | Theorems.Thm_PGDRevision20261113_finite_feature_rate_sublevels
-- name    : PGDRevision20261113.finite_feature_rate_sublevels
-- status  : Proved
-- author  : @Somehow
-- created : 2026-11-13T06:24:13.184708+00:00
-- url     : https://prove2.me/theorems/4dd784f1-031f-48f0-b0d2-951480e5aee4
-- title:
--   Convex rate sublevels for finite-feature geometry design
-- statement:
--   On $\mathbb R$, let $f,g\in C^2$ have curvatures $A=f''\ge0$ and $B=g''\ge\lambda>0$, with $A$ bounded. Let $g_1,\ldots,g_d$ be fixed continuously differentiable features satisfying $g_j(0)=0$. For $\theta\in\mathbb R^d$ and $u\in\mathbb R$, set
--   $$
--   k_\theta(t)=\exp\!\left(\sum_j\theta_jg_j(t)\right),\qquad p=e^u.
--   $$
--   Take the twice integrated curvature as the generator, and use the real implicit update for $f+g+\ell t$. Every update exists uniquely. Put
--   $$
--   \rho(u,\theta)=\sup_{t\in\mathbb R}
--   \left|\frac{e^u k_\theta(t)-A(t)}{e^u k_\theta(t)+B(t)}\right|.
--   $$
--   For $0<R<1$, define $L_t(R)=(A(t)-RB(t))/(1+R)$ and $U_t(R)=(A(t)+RB(t))/(1-R)$. Then $\rho(u,\theta)\le R$ is equivalent to the following constraints for every real state:
--   $$
--   u+\sum_j\theta_jg_j(t)\le\log U_t(R),
--   $$
--   $$
--   u+\sum_j\theta_jg_j(t)\ge\log L_t(R)
--   \quad\text{whenever }A(t)>RB(t).
--   $$
--   Thus each rate sublevel is convex, including its intersection with any convex coefficient domain. These are constraints on the full state domain; a finite grid does not by itself certify them.
--
--   **Related results.** [Exact profile performance (Theorem 4.1)](https://prove2.me/theorems/b4a2818b-e88a-4b19-b714-efb466e89aa9) · [Geometry classification (Theorem 5.1)](https://prove2.me/theorems/7c34b392-dd3f-4671-be5a-26a7d75835ba) · [Parameter localization (Theorem 7.1)](https://prove2.me/theorems/b35f0a31-5173-472e-a00e-338bd545e1ef)
--
--   **Further examples and certificates.** [finite feature nonuniqueness counterexample](https://prove2.me/theorems/48884d70-daa8-4d9b-a622-d0e2e9b388f9) · [loss matched one step](https://prove2.me/theorems/5cea0578-3f05-4c5f-a562-c9030062bf32)
-- source:
--   Author manuscript: Exact Residual Bounds and Optimal Geometry Selection for Proximal Gradient Methods, revised reading edition, 13 November 2026, Proposition 4.3, p. 11; source file sections/04_bregman_framework.tex, label prop:feature_design.

import Definitions.Def_PGDRevision20261113_Profile
open PGDRevision20261113

theorem PGDRevision20261113.finite_feature_rate_sublevels : FiniteFeatureDesignClaim := by sorry
