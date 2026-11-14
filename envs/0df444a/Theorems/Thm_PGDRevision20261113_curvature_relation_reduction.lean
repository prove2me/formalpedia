-- Prove2me | Theorems.Thm_PGDRevision20261113_curvature_relation_reduction
-- name    : PGDRevision20261113.curvature_relation_reduction
-- status  : Proved
-- author  : @Somehow
-- created : 2026-11-13T06:26:12.66665+00:00
-- url     : https://prove2.me/theorems/569bd574-8d1b-4c8d-8e71-3c2b232c84f0
-- title:
--   Geometry design depends only on the curvature relation
-- statement:
--   Consider the real-line penalty-curvature model of the geometry-classification theorem. Thus $A\ge0$ is bounded, nonzero and continuously differentiable; $\lambda>0$; $b\in C^1$ has $b(0)=1<b(x)$ for $x\ne0$, derivative negative to the left and positive to the right of zero, and diverges at both ends. Let $k_c=b^c$ for $c\ge0$.
--
--   If $A(x)=a(b(x))$, then for all $c\ge0$ and $p>0$,
--   $$
--   \boxed{
--   \rho(c,p)=\sup_{s\ge1}
--   \left|\frac{ps^c-a(s)}{ps^c+\lambda s}\right|.}
--   $$
--   Consequently the exact rate and optimal parameter pair depend only on $a$ and $\lambda$, independently of the spatial shape of $b$. In particular, two admissible real-line models with the same $a$ and $\lambda$ have exactly the same optimizing pairs.
--
--   This comparison prescribes the loss as $a\circ b$ together with the penalty shape.
--
--   **Related results.** [Exact profile performance (Theorem 4.1)](https://prove2.me/theorems/b4a2818b-e88a-4b19-b714-efb466e89aa9) · [Geometry classification (Theorem 5.1)](https://prove2.me/theorems/7c34b392-dd3f-4671-be5a-26a7d75835ba)
--
--   **Further examples and certificates.** [polynomial penalty models](https://prove2.me/theorems/7745bf8d-dbbf-4bb6-81d3-be854efa3535) · [polynomial quadratic geometry examples](https://prove2.me/theorems/56fed2bb-bdce-4491-8f05-d5959791e9df) · [polynomial matched geometry examples](https://prove2.me/theorems/eb4d825a-2db0-4a60-95f4-1bbe39101c23) · [polynomial interior geometry examples](https://prove2.me/theorems/dc636fa7-9f09-4d18-b4eb-061ec9356983)
-- source:
--   Author manuscript: Exact Residual Bounds and Optimal Geometry Selection for Proximal Gradient Methods, revised reading edition, 13 November 2026, Corollary 6.3, p. 17; source file sections/06_classification_applications.tex, label cor:curvature_relation.

import Definitions.Def_PGDRevision20261113_Geometry
open PGDRevision20261113

theorem PGDRevision20261113.curvature_relation_reduction : CurvatureRelationClaim := by sorry
