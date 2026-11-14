-- Prove2me | Theorems.Thm_PGDRevision20261113_separable_profiles
-- name    : PGDRevision20261113.separable_profiles
-- status  : Proved
-- author  : @Somehow
-- created : 2026-11-13T06:24:16.093801+00:00
-- url     : https://prove2.me/theorems/78750d96-d9de-46a8-8659-77376dd8fedc
-- title:
--   Exact performance for separable profiles
-- statement:
--   Let $d\ge1$, and let $f_j,g_j,\phi_j$ be scalar profiles on open intervals $I_j$, for $1\le j\le d$. Fix one inverse stepsize $p>0$, and assume that every scalar profile satisfies the hypotheses of the exact-profile theorem: twice continuous differentiability, $A_j=f_j''\ge0$, $B_j=g_j''\ge0$, $A_j+B_j>0$, $k_j=\phi_j''>0$, and surjectivity of $p\phi_j'+g_j'$ onto $\mathbb R$.
--
--   Use separable functions $f=\sum_jf_j$, $g=\sum_jg_j$, $\phi=\sum_j\phi_j$ on the product interval and the actual coordinatewise implicit update. For $F_\ell=f+g+\langle\ell,x\rangle$, allow any $\ell\in\mathbb R^d$ and initial state with nonzero gradient. Define
--   $$
--   \rho_j=\sup_{t\in I_j}
--   \left|\frac{pk_j(t)-A_j(t)}{pk_j(t)+B_j(t)}\right|.
--   $$
--   For every finite $N\ge1$, the exact squared Euclidean gradient ratio is
--   $$
--   \boxed{
--   \sup_{\ell,x_0:\,\nabla F_\ell(x_0)\ne0}
--   \frac{\|\nabla F_\ell(x_N)\|^2}{\|\nabla F_\ell(x_0)\|^2}
--   =\max_{1\le j\le d}\rho_j^{2N}.}
--   $$
--   Infinite values are interpreted in the extended nonnegative reals. This is the product-profile extension of the scalar exact-performance result.
--
--   **Related results.** [Exact profile performance (Theorem 4.1)](https://prove2.me/theorems/b4a2818b-e88a-4b19-b714-efb466e89aa9) · [Geometry classification (Theorem 5.1)](https://prove2.me/theorems/7c34b392-dd3f-4671-be5a-26a7d75835ba) · [Parameter localization (Theorem 7.1)](https://prove2.me/theorems/b35f0a31-5173-472e-a00e-338bd545e1ef)
-- source:
--   Author manuscript: Exact Residual Bounds and Optimal Geometry Selection for Proximal Gradient Methods, revised reading edition, 13 November 2026, Corollary 4.2, p. 11; source file sections/04_bregman_framework.tex, label cor:bg_separable.

import Definitions.Def_PGDRevision20261113_Profile
open PGDRevision20261113

theorem PGDRevision20261113.separable_profiles : SeparableProfilesClaim := by sorry
