-- Prove2me | Theorems.Thm_PGDRevision20261113_affine_loss_nonattainment
-- name    : PGDRevision20261113.affine_loss_nonattainment
-- status  : Proved
-- author  : @Somehow
-- created : 2026-11-13T08:07:58.973498+00:00
-- url     : https://prove2.me/theorems/50fa751b-c410-4059-9fab-7ac19b6f8dfc
-- title:
--   The affine-loss case has zero infimum and no minimizing pair
-- statement:
--   Take $A\equiv0$ and $\lambda>0$. In the interval family let $b=k_\beta$ with $\beta\ge1$; in the real-line family it suffices that $b\ge1$ and $b(0)=1$. For $c\ge0,p>0$, define the usual error using $k_c$ on the interval, or $k_c=b^c$ on the line.
--
--   Every feasible pair has strictly positive error norm. Quadratic geometry satisfies
--   $$\rho(0,p)=\frac{p}{p+\lambda},$$
--   and for every $\varepsilon>0$ some $p>0$ makes this norm smaller than $\varepsilon$. Consequently the global infimum is zero and no feasible pair attains it.
--
--   **Related results.** [Exact profile performance (Theorem 4.1)](https://prove2.me/theorems/b4a2818b-e88a-4b19-b714-efb466e89aa9) · [Geometry classification (Theorem 5.1)](https://prove2.me/theorems/7c34b392-dd3f-4671-be5a-26a7d75835ba)
-- source:
--   Author manuscript, Exact Residual Bounds and Optimal Geometry Selection for Proximal Gradient Methods, revised reading edition, 13 November 2026; Section 5, paragraph following the classification proof; sections/05_geometry_classification.tex, For the excluded affine case.

import Definitions.Def_PGDRevision20261113_Examples
open PGDRevision20261113

theorem PGDRevision20261113.affine_loss_nonattainment : AffineLossNonattainmentClaim := by sorry
