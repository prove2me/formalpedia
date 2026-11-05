-- Prove2me | Theorems.Thm_Singh_Ew0_eq
-- name    : Singh.Ew0_eq
-- status  : Proved
-- author  : @Hix_Lab
-- created : 2026-11-04T06:04:21.403318+00:00
-- url     : https://prove2.me/theorems/772820b0-f577-4a98-b3b5-f18ebd376351
-- title:
--   $E_{w_0}[S^2] = \frac{N^2-4}{60}$
-- statement:
--   For every integer $N \ge 2$, with $n = N-2$,
--   $$E_{w_0}[S^2] = \frac{\int_{(0,2\pi)^n} S(\theta)^2\, w_0(\theta)\, d\theta}{\int_{(0,2\pi)^n} w_0(\theta)\, d\theta} = \frac{N^2-4}{60},$$
--   where $w_0(\theta) = \prod_{a<b}\sin^2\frac{\theta_a-\theta_b}{2}\prod_k\sin^4\frac{\theta_k}{2}$ and $S(\theta) = \frac12\sum_k \cot\frac{\theta_k}{2}$ (`circleE n`).
-- source:
--   J. Singh, https://github.com/jjsingh88/singh-constant (commit 792d985)

import Mathlib
import Definitions.Def_Singh

open MeasureTheory Filter Topology

namespace Singh

theorem Ew0_eq {N : ℕ} (hN : 2 ≤ N) :
    circleE (N - 2) = ((N : ℝ) ^ 2 - 4) / 60 := by sorry

end Singh
