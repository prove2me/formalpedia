-- Prove2me | Theorems.Thm_PGDRevision20261113_ordered_kernel_ratio
-- name    : PGDRevision20261113.ordered_kernel_ratio
-- status  : Proved
-- author  : @Somehow
-- created : 2026-11-13T06:24:16.484893+00:00
-- url     : https://prove2.me/theorems/442508d0-c950-482c-a550-770198843e70
-- title:
--   Scaled kernel ratios are strictly ordered by the state feature
-- statement:
--   Use either admissible geometry model of Theorem 5.1, with ordering feature $\zeta$ and positive kernels $k_c$. Let $0\le c_1<c_2$ and $p_1,p_2>0$. Whenever two states satisfy $\zeta(x)<\zeta(y)$,
--   $$
--   \frac{p_2k_{c_2}(x)}{p_1k_{c_1}(x)}
--   <
--   \frac{p_2k_{c_2}(y)}{p_1k_{c_1}(y)}.
--   $$
--   For the interval model $\zeta(t)=|t|$ and $k_c(t)=((1+t)^{-c}+(1-t)^{-c})/2$; for the real-line model $\zeta(x)=\log b(x)$ and $k_c(x)=b(x)^c$.
--   This is the ordered-kernel comparison used by the classification certificates.
--
--   **Related results.** [Exact profile performance (Theorem 4.1)](https://prove2.me/theorems/b4a2818b-e88a-4b19-b714-efb466e89aa9) · [Geometry classification (Theorem 5.1)](https://prove2.me/theorems/7c34b392-dd3f-4671-be5a-26a7d75835ba)
-- source:
--   Author manuscript: Exact Residual Bounds and Optimal Geometry Selection for Proximal Gradient Methods, revised reading edition, 13 November 2026, Theorem 5.1 proof, kernel facts, pages 13-14.

import Definitions.Def_PGDRevision20261113_Geometry
open PGDRevision20261113

theorem PGDRevision20261113.ordered_kernel_ratio : OrderedKernelRatioClaim := by sorry
