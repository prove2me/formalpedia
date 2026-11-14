-- Prove2me | Theorems.Thm_PGDRevision20261113_dca_convex_objective_bound
-- name    : PGDRevision20261113.dca_convex_objective_bound
-- status  : Open
-- author  : @Somehow
-- created : 2026-11-13T06:24:15.471682+00:00
-- url     : https://prove2.me/theorems/e3e025c6-9daa-4674-9822-101af7c37875
-- title:
--   The DCA mapping bound on the convex-objective branch
-- statement:
--   Let $u:\mathbb R^d\to(-\infty,+\infty]$ be proper, closed and $\mu_1$-strongly convex. Let $v:\mathbb R^d\to\mathbb R$ be differentiable, with both
--   $$
--   v-\frac{\mu_2}{2}\|\cdot\|^2,\qquad
--   \frac{L_2}{2}\|\cdot\|^2-v
--   $$
--   convex. Assume
--   $$
--   \mu_1>0,\qquad \mu_2<L_2\le\mu_1,\qquad \mu_1+\mu_2>0.
--   $$
--   Write $H=u-v$. Starting from $x_0\in\operatorname{dom}u$, perform $N\ge2$ DCA updates satisfying
--   $$
--   0\in\partial u(x_{i+1})-\nabla v(x_i)\quad(0\le i<N).
--   $$
--   For $k\ge1$, let $E_k(z)=\sum_{j=1}^{2k}z^{-j}$ when $z\ne0$, and $E_k(0)=+\infty$. The terminal displacement obeys
--   $$
--   \boxed{\frac{\mu_1}{2}\|x_{N-1}-x_N\|^2
--   \le
--   \frac{H(x_0)-H(x_N)}
--   {1+\mu_2/\mu_1+
--   \min\{E_{N-1}(L_2/\mu_1),E_{N-1}(\mu_2/\mu_1)\}}.}
--   $$
--   The minimum-displacement bound follows on the same parameter region. This statement covers the complete convex-objective branch, including both signs of $L_2+\mu_2$.
--
--   **Formalization Note.** The DCA subgradient inclusion is represented by minimization of the convex function $u-\langle\nabla v(x_i),\cdot\rangle$. The zero-argument energy is encoded as extended-real infinity before taking the minimum.
--
--   **Related results.** [Fixed-penalty exact curve](https://prove2.me/theorems/74766593-41e8-45f7-ae2a-cb31e0cc04ec) · [Optimal constant stepsizes](https://prove2.me/theorems/592366ff-6e05-4633-8520-4428630b7e49)
-- source:
--   Author manuscript: Exact Residual Bounds and Optimal Geometry Selection for Proximal Gradient Methods, revised reading edition, 13 November 2026, Corollary 2.8, p. 7; source file sections/02_dca_consequence.tex, label cor:dca.

import Definitions.Def_PGDRevision20261113_Euclidean
open PGDRevision20261113

theorem PGDRevision20261113.dca_convex_objective_bound : DCAConvexObjectiveClaim := by sorry
