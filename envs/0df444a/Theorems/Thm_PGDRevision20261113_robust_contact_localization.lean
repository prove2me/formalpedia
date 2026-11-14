-- Prove2me | Theorems.Thm_PGDRevision20261113_robust_contact_localization
-- name    : PGDRevision20261113.robust_contact_localization
-- status  : Open
-- author  : @Somehow
-- created : 2026-11-13T08:08:25.701928+00:00
-- url     : https://prove2.me/theorems/724e9a21-4672-4c25-9520-1aa705293868
-- title:
--   Certified upper and lower constants preserve the localization bounds
-- statement:
--   For a positive kernel $k_c(t)$, error $E=(pk_c-A)/(pk_c+B)$, and $0<R<1$, write
--   $$\mathcal L_t(R)=\frac{A(t)-RB(t)}{1+R},\quad
--   \mathcal U_t(R)=\frac{A(t)+RB(t)}{1-R}.$$
--   For fixed ordered contacts $t_1,t_2,t_3$ with signs $s_i=\sigma(-1)^{i-1}$, let
--   $$\beta_i=\begin{cases}\log\mathcal U_{t_i}(U)-\log\mathcal U_{t_i}(L),&s_i=1,\\
--   \log\mathcal L_{t_i}(L)-\log\mathcal L_{t_i}(U),&s_i=-1.\end{cases}$$
--
--   Assume all hypotheses of the approximate-contact localization theorem on a compact parameter interval $C$, including candidate $(\widehat c,\widehat p)$, signed contact lower bound $L$, global upper bound $U<1$, and positive lower bands at negative contacts. Replace $\beta_i$ by upper bounds $\bar\beta_i$, each adjacent minimum score gap by a positive lower bound $\underline\delta_{ij}$, and the contact score norm by an upper bound $\bar M$.
--
--   For $\sigma=1$, put $d_-=(\bar\beta_1+\bar\beta_2)/\underline\delta_{12}$ and $d_+=(\bar\beta_2+\bar\beta_3)/\underline\delta_{23}$; for $\sigma=-1$, interchange these two radii. Every pair $c\in C,p>0$ with norm at most $U$ satisfies
--   $$\widehat c-d_-\le c\le\widehat c+d_+,\qquad
--   |\log(p/\widehat p)|\le\max_i\bar\beta_i+\bar M\max(d_-,d_+).$$
--
--   **Related results.** [Parameter localization (Theorem 7.1)](https://prove2.me/theorems/b35f0a31-5173-472e-a00e-338bd545e1ef) · [Error-band equivalence](https://prove2.me/theorems/672f9ba5-f16d-4b26-bfdf-ed78d3d74fd5)
-- source:
--   Author manuscript, Exact Residual Bounds and Optimal Geometry Selection for Proximal Gradient Methods, revised reading edition, 13 November 2026; Section 7, paragraph following the localization proof; sections/07_quantitative_certificates.tex, The bounds remain valid.

import Definitions.Def_PGDRevision20261113_NumericalCertificates
open PGDRevision20261113

theorem PGDRevision20261113.robust_contact_localization : RobustContactLocalizationClaim := by sorry
