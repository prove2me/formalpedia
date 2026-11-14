-- Prove2me | Theorems.Thm_PGDRevision20261113_power_series_coefficient_ratios
-- name    : PGDRevision20261113.power_series_coefficient_ratios
-- status  : Open
-- author  : @Somehow
-- created : 2026-11-13T06:24:21.845878+00:00
-- url     : https://prove2.me/theorems/4e3c5465-6520-4088-8caf-66cae2bf90ce
-- title:
--   Increasing coefficient ratios for the power-curvature series
-- statement:
--   For $0<c<1$, define
--   $$
--   k_c(t)=\tfrac12[(1+t)^{-c}+(1-t)^{-c}],
--   \qquad d_n=\frac{(c)_{2n}}{(2n)!},
--   \qquad r_n=\frac{d_n}{d_{n-1}}\quad(n\ge1),
--   $$
--   where $(c)_m=\prod_{j=0}^{m-1}(c+j)$ is the rising product. Then $d_0=1$,
--   $$
--   r_n=\frac{(c+2n-2)(c+2n-1)}{2n(2n-1)},
--   \qquad r_1=\frac{c(c+1)}2,
--   $$
--   and the sequence $(r_n)_{n\ge1}$ is strictly increasing with limit one.
--
--   For every $0\le u<1$, the convergent expansions are
--   $$
--   k_c(\sqrt u)=\sum_{n\ge0}d_nu^n,
--   $$
--   and, for $a\in(0,1)$,
--   $$
--   (1-au)k_c(\sqrt u)
--   =1+\sum_{n\ge1}d_{n-1}(r_n-a)u^n.
--   $$
--   This records the coefficient and expansion part of Lemma 6.2. The threshold-monotonicity and one-turning-point conclusion already has an existing Prove2Me target.
--
--   **Related results.** [Existing power-curvature threshold](https://prove2.me/theorems/42737d46-8bb5-4759-b1d2-a65ca8ede81a) · [Entropy-mixture specialization](https://prove2.me/theorems/16d88707-66f2-4072-abc1-4e0089053379) · [Geometry classification (Theorem 5.1)](https://prove2.me/theorems/7c34b392-dd3f-4671-be5a-26a7d75835ba)
-- source:
--   Author manuscript: Exact Residual Bounds and Optimal Geometry Selection for Proximal Gradient Methods, revised reading edition, 13 November 2026, Lemma 6.2, p. 16; source file sections/06_classification_applications.tex, label lem:threshold.

import Definitions.Def_PGDRevision20261113_Series
open PGDRevision20261113

theorem PGDRevision20261113.power_series_coefficient_ratios : PowerSeriesCoefficientRatiosClaim := by sorry
