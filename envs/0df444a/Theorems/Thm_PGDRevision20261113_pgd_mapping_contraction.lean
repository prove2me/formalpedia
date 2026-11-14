-- Prove2me | Theorems.Thm_PGDRevision20261113_pgd_mapping_contraction
-- name    : PGDRevision20261113.pgd_mapping_contraction
-- status  : Open
-- author  : @Somehow
-- created : 2026-11-13T06:24:20.740253+00:00
-- url     : https://prove2.me/theorems/72c5911d-09f7-4a1e-91d7-cbe546a6398a
-- title:
--   Contraction of the PGD update and monotonicity of executed mappings
-- statement:
--   Let $f:\mathbb R^d\to\mathbb R$ be convex and differentiable with an $L$-Lipschitz gradient, where $L>0$. Let $r$ be proper, closed and $\mu$-strongly convex, with $\mu\ge0$. Fix $\gamma>0$ with $0<\gamma L<2$, and define
--   $$
--   T(x)=\operatorname{prox}_{\gamma r}(x-\gamma\nabla f(x)),
--   \qquad G_\gamma(x)=\frac{x-T(x)}{\gamma}.
--   $$
--   The update map obeys the global contraction bound
--   $$
--   \|T(x)-T(y)\|\le\frac{\|x-y\|}{1+\gamma\mu}.
--   $$
--   Consequently, along any $N\ge1$ successive updates $x_{i+1}=T(x_i)$,
--   $$
--   \|G_\gamma(x_{i+1})\|\le
--   \frac{\|G_\gamma(x_i)\|}{1+\gamma\mu}\quad(0\le i<N-1),
--   \qquad
--   \min_{0\le i<N}\|G_\gamma(x_i)\|=\|G_\gamma(x_{N-1})\|.
--   $$
--   Thus the best executed mapping and the terminal executed mapping have the same norm. The penalty need not have a non-singleton domain for this contraction statement.
--
--   **Related results.** [Fixed-penalty exact curve](https://prove2.me/theorems/74766593-41e8-45f7-ae2a-cb31e0cc04ec) · [Optimal constant stepsizes](https://prove2.me/theorems/592366ff-6e05-4633-8520-4428630b7e49)
-- source:
--   Author manuscript: Exact Residual Bounds and Optimal Geometry Selection for Proximal Gradient Methods, revised reading edition, 13 November 2026, Lemma 2.2, p. 3; source file sections/02_exact_curve.tex, label lem:lastmapping.

import Definitions.Def_PGDRevision20261113_Euclidean
open PGDRevision20261113

theorem PGDRevision20261113.pgd_mapping_contraction : MappingContractionClaim := by sorry
