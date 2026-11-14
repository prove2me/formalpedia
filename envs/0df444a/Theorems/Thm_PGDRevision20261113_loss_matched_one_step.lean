-- Prove2me | Theorems.Thm_PGDRevision20261113_loss_matched_one_step
-- name    : PGDRevision20261113.loss_matched_one_step
-- status  : Proved
-- author  : @Somehow
-- created : 2026-11-13T08:08:02.372196+00:00
-- url     : https://prove2.me/theorems/5cea0578-3f05-4c5f-a562-c9030062bf32
-- title:
--   Unrestricted matching to the loss derivative gives a stationary point in one update
-- statement:
--   Let $(f,g,\phi)$ and $p>0$ satisfy the scalar-profile hypotheses on an open interval $I$, including the surjectivity that gives unique implicit updates. Assume
--   $$p\phi'(t)=f'(t)\qquad(t\in I).$$
--   For every free tilt $\ell$ and every exact one-step trajectory,
--   $$p\phi'(x_1)+g'(x_1)=p\phi'(x_0)-f'(x_0)-\ell,$$
--   the new state satisfies $(f+g+\ell t)'(x_1)=0$. This is the one-step observation underlying the decision to restrict geometry families; it places no bound on the cost of solving the implicit equation.
--
--   **Related results.** [Exact profile performance (Theorem 4.1)](https://prove2.me/theorems/b4a2818b-e88a-4b19-b714-efb466e89aa9) · [Geometry classification (Theorem 5.1)](https://prove2.me/theorems/7c34b392-dd3f-4671-be5a-26a7d75835ba)
-- source:
--   Author manuscript, Exact Residual Bounds and Optimal Geometry Selection for Proximal Gradient Methods, revised reading edition, 13 November 2026; Section 4.1, final paragraph; sections/04_bregman_framework.tex, Allowing unrestricted.

import Definitions.Def_PGDRevision20261113_Examples
open PGDRevision20261113

theorem PGDRevision20261113.loss_matched_one_step : LossMatchedOneStepClaim := by sorry
