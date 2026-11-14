-- Prove2me | Theorems.Thm_PGDRevision20261113_positive_measure_entropy_extension
-- name    : PGDRevision20261113.positive_measure_entropy_extension
-- status  : Open
-- author  : @Somehow
-- created : 2026-11-13T08:08:19.438744+00:00
-- url     : https://prove2.me/theorems/cbb9835f-44dc-466c-a418-060ff9eb0673
-- title:
--   The entropy-mixture theorem extends to finite positive measures
-- statement:
--   Let $\nu$ be a finite positive measure on $\mathbb R$, supported in $[0,\bar a]$ with $0<\bar a<1$, and suppose $\int a\,d\nu>0$. Let $\lambda>0$ and put
--   $$
--   H(t)=\tfrac12[(1+t)\log(1+t)+(1-t)\log(1-t)],\quad
--   \psi(t)=\int H(\sqrt a\,t)\,d\nu(a),\quad
--   A(t)=\int\frac{a}{1-at^2}\,d\nu(a).
--   $$
--   On $(-1,1)$ the penalty is $\lambda H$ and the candidate curvature is $k_c=\tfrac12[(1+t)^{-c}+(1-t)^{-c}]$. These data are admissible, $\psi''=A$, and the exact relative-gradient criterion is $\Omega_N(c,p)=\rho(c,p)^{2N}$ for $c\ge0,p>0,N\ge1$.
--
--   Write $A_0=\int a\,d\nu$, $A_1=\int a/(1-a)\,d\nu$, and $\chi(a)=(\sqrt{1+8a}-1)/2$. There is a unique global minimizing pair, with
--   $$
--   0<c_*<\chi(\bar a)<1,\quad A_0/2<p_*<A_1,\quad
--   0<\rho_*<\frac{A_0}{A_0+2\lambda}<1.
--   $$
--   It has three alternating nonnegative radii under its global envelope; conversely such contacts certify the unique optimum. It strictly beats separately optimized quadratic and matched geometries, and uniquely minimizes every finite horizon. When the integrated loss is the single normalized profile $H(\sqrt a\,t)$, the sharper scale bounds $a<p_*<a/(1-a)$ and $+,-,+$ contacts starting at zero hold as well.
--
--   **Related results.** [Finite entropy-mixture optimum](https://prove2.me/theorems/16d88707-66f2-4072-abc1-4e0089053379) · [Geometry classification (Theorem 5.1)](https://prove2.me/theorems/7c34b392-dd3f-4671-be5a-26a7d75835ba) · [Exact profile performance (Theorem 4.1)](https://prove2.me/theorems/b4a2818b-e88a-4b19-b714-efb466e89aa9)
-- source:
--   Author manuscript, Exact Residual Bounds and Optimal Geometry Selection for Proximal Gradient Methods, revised reading edition, 13 November 2026; Section 6.1, paragraph following the proof of Theorem 6.1; sections/06_classification_applications.tex, The argument also permits finite positive measures.

import Definitions.Def_PGDRevision20261113_MeasureExtension
open PGDRevision20261113

theorem PGDRevision20261113.positive_measure_entropy_extension : PositiveMeasureEntropyExtensionClaim := by sorry
