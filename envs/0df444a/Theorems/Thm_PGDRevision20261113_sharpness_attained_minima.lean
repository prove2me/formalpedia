-- Prove2me | Theorems.Thm_PGDRevision20261113_sharpness_attained_minima
-- name    : PGDRevision20261113.sharpness_attained_minima
-- status  : Open
-- author  : @Somehow
-- created : 2026-11-13T06:24:19.572849+00:00
-- url     : https://prove2.me/theorems/507ef5c0-9a5e-45e5-86c0-e5588dab7c48
-- title:
--   Fixed-penalty sharpness with attained objective minima
-- statement:
--   Let $r$ be a prescribed proper closed convex penalty with non-singleton domain in a fixed Euclidean dimension, and let $\mu_r$ be its best global strong-convexity modulus. Fix $L>0$, $N\ge1$, $0<h<2$ and $\gamma=h/L$. For a globally convex $L$-smooth function $f$, run proximal gradient on $F=f+r$ from any feasible initial point.
--
--   Restrict the admissible smooth functions to those for which $F$ attains a global minimum, and retain only trajectories with $F(x_0)>F(x_N)$. Then
--   $$
--   \sup_{\substack{f\in\mathcal F_{0,L},\ x_0\in\operatorname{dom}r\\
--   f+r\text{ attains a global minimum}\\F(x_0)>F(x_N)}}
--   \frac{\|G_\gamma(x_{N-1})\|^2}{L[F(x_0)-F(x_N)]}
--   =K_N(h,\mu_r/L).
--   $$
--   The dimension and penalty remain fixed in the supremum. Equality is equality of least upper bounds and does not assert that every fixed penalty has a maximizing instance. This identifies the same exact curve under an additional attained-minimum restriction.
--
--   **Related results.** [Fixed-penalty exact curve](https://prove2.me/theorems/74766593-41e8-45f7-ae2a-cb31e0cc04ec) · [Optimal constant stepsizes](https://prove2.me/theorems/592366ff-6e05-4633-8520-4428630b7e49)
-- source:
--   Author manuscript: Exact Residual Bounds and Optimal Geometry Selection for Proximal Gradient Methods, revised reading edition, 13 November 2026, Corollary 2.7, p. 7; source file sections/02_exact_curve.tex, label cor:attained.

import Definitions.Def_PGDRevision20261113_Euclidean
open PGDRevision20261113

theorem PGDRevision20261113.sharpness_attained_minima : SharpnessAttainedMinimaClaim := by sorry
