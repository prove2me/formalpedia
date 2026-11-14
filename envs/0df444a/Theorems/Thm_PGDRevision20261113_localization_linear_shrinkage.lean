-- Prove2me | Theorems.Thm_PGDRevision20261113_localization_linear_shrinkage
-- name    : PGDRevision20261113.localization_linear_shrinkage
-- status  : Open
-- author  : @Somehow
-- created : 2026-11-13T08:08:15.004296+00:00
-- url     : https://prove2.me/theorems/c154b1dc-ce78-497b-b2ef-171db972e468
-- title:
--   Fixed-contact localization boxes shrink linearly with the rate gap
-- statement:
--   For a positive kernel $k_c(t)$, error $E=(pk_c-A)/(pk_c+B)$, and $0<R<1$, write
--   $$\mathcal L_t(R)=\frac{A(t)-RB(t)}{1+R},\quad
--   \mathcal U_t(R)=\frac{A(t)+RB(t)}{1-R}.$$
--   For fixed ordered contacts $t_1,t_2,t_3$ with signs $s_i=\sigma(-1)^{i-1}$, let
--   $$\beta_i=\begin{cases}\log\mathcal U_{t_i}(U)-\log\mathcal U_{t_i}(L),&s_i=1,\\
--   \log\mathcal L_{t_i}(L)-\log\mathcal L_{t_i}(U),&s_i=-1.\end{cases}$$
--
--   Fix the contact states, signs, compact parameter interval, and a kernel satisfying the score-ordering hypotheses. Fix $0<r_0\le r_1<1$, and require $A(t_i)>r_1B(t_i)$ at every negative contact.
--
--   There is a constant $K\ge0$, independent of $L,U$, such that for every $r_0\le L\le U\le r_1$, each $\beta_i$, both exponent radii $d_-,d_+$, and the logarithmic scale radius are nonnegative and at most
--   $$K(U-L).$$
--   This states the linear shrinking assertion with uniform positivity of all relevant band denominators. The contacts and interval remain fixed while the two rate levels vary.
--
--   **Related results.** [Parameter localization (Theorem 7.1)](https://prove2.me/theorems/b35f0a31-5173-472e-a00e-338bd545e1ef) · [Error-band equivalence](https://prove2.me/theorems/672f9ba5-f16d-4b26-bfdf-ed78d3d74fd5)
-- source:
--   Author manuscript, Exact Residual Bounds and Optimal Geometry Selection for Proximal Gradient Methods, revised reading edition, 13 November 2026; Section 7, paragraph following the rational scale enclosure; sections/07_quantitative_certificates.tex, all beta_i=O(U-L).

import Definitions.Def_PGDRevision20261113_NumericalCertificates
open PGDRevision20261113

theorem PGDRevision20261113.localization_linear_shrinkage : LocalizationLinearShrinkageClaim := by sorry
