-- Prove2me | Theorems.Thm_Viterbo_cEHZ_capacityBall
-- name    : Viterbo.cEHZ_capacityBall
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T08:15:08.093566+00:00
-- url     : https://prove2.me/theorems/ccde4d67-0c4b-41fd-af30-b3526234e6a5
-- title:
--   Proof of Theorem 1.3 — the ball B²ⁿ(r) has Ekeland–Hofer–Zehnder capacity πr²
-- statement:
--   For every $n \ge 1$ and $r > 0$, the open Euclidean ball $B^{2n}(r) \subset \mathbb R^{2n}$ has $c_{\rm EHZ}(B^{2n}(r)) = \pi r^2$.
-- source:
--   Haim-Kislev, P. and Ostrover, Y., A counterexample to Viterbo's conjecture, Ann. of Math. (2) 203 (2026) 603–622, https://doi.org/10.4007/annals.2026.203.2.5 (arXiv:2405.16513v3, whose page numbers are used), p. 5, the capacity of the ball in the proof of Theorem 1.3

import Mathlib
import Definitions.Def_SymmetricPolar
import Definitions.Def_Viterbo

namespace Viterbo

theorem cEHZ_capacityBall (n : ℕ) (hn : 1 ≤ n) (r : ℝ) (hr : 0 < r) :
    cEHZ (OAI.SymmetricPolar.capacityBall n (Real.pi * r ^ 2)) = ENNReal.ofReal (Real.pi * r ^ 2) := by
  sorry

end Viterbo
