-- Prove2me | Theorems.Thm_Viterbo_volume_pentagon_and_systolicRatio_pentagonK_prod_pentagonT
-- name    : Viterbo.volume_pentagon_and_systolicRatio_pentagonK_prod_pentagonT
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T08:14:43.465139+00:00
-- url     : https://prove2.me/theorems/5acb79c7-a903-4d84-a135-f8ea2f4be245
-- title:
--   Proof of Theorem 1.3, n = 2 — Area(K) = Area(T) = (5/2)sin(2π/5) and Sys(K × T) = (√5 + 3)/5 > 1
-- statement:
--   For the two pentagons $K$ and $T$: both have area $\frac52\sin(\frac{2\pi}{5})$, and the systolic ratio of $K \times T \subset \mathbb R^4$ is $\mathrm{Sys}(K \times T) = c_{\rm EHZ}(K \times T)^2/(2\,\mathrm{Vol}(K \times T)) = \frac{\sqrt5 + 3}{5}$, which is greater than $1$.
-- source:
--   Haim-Kislev, P. and Ostrover, Y., A counterexample to Viterbo's conjecture, Ann. of Math. (2) 203 (2026) 603–622, https://doi.org/10.4007/annals.2026.203.2.5 (arXiv:2405.16513v3, whose page numbers are used), p. 5, the case n = 2 of the proof of Theorem 1.3

import Mathlib
import Definitions.Def_Viterbo

open MeasureTheory

namespace Viterbo

theorem volume_pentagon_and_systolicRatio_pentagonK_prod_pentagonT :
    volume pentagonK = ENNReal.ofReal (5 / 2 * Real.sin (2 * Real.pi / 5)) ∧
      volume pentagonT = ENNReal.ofReal (5 / 2 * Real.sin (2 * Real.pi / 5)) ∧
      systolicRatio (pentagonK ×ˢ pentagonT) = ENNReal.ofReal ((Real.sqrt 5 + 3) / 5) ∧
      1 < systolicRatio (pentagonK ×ˢ pentagonT) := by
  sorry

end Viterbo
