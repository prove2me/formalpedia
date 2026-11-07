-- Prove2me | Theorems.Thm_SoftmaxAttnFD_proposition_5_5
-- name    : SoftmaxAttnFD.proposition_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:05:05.459986+00:00
-- url     : https://prove2.me/theorems/2259b498-b0d5-4593-87e0-68bba6332ff5
-- title:
--   Proposition 5.5, p.21 — from $\mathrm{BP}_{d-1}$ to $\mathrm{KP}_d$
-- statement:
--   Let $d\ge3$. If $\mathrm{BP}_{d-1}$ can be solved by a Las Vegas algorithm in expected time $\tilde O(F_d(m,n))$, then $\mathrm{KP}_d$ can be solved by a Las Vegas algorithm in the same expected time.
--   This is the temperature-interpolation half of one induction step.
--
--   Differences from the source:
--   - encoding: "can be solved by a Las Vegas algorithm in expected time Õ(F_d(m, n))" → BPSolvable d → KPSolvable d, each with its own program, C and K; reason: the page names no machine (Machine), and soft-O has constants fixed before the instance
-- source:
--   Huang, Chen, Softmax Attention with Any Temperature in Fixed Dimension, arXiv:2611.06055 (sha256 a60f7609…), Proposition 5.5, p.21

import Definitions.Def_SoftmaxAttnFD_BiasedProducts

namespace SoftmaxAttnFD

/-- **Proposition 5.5** (arXiv:2611.06055, sha256 a60f7609…, p.21). Let `d ≥ 3`. If `BP_{d−1}` can be
solved by a Las Vegas algorithm in expected time `Õ(F_d(m, n))`, then `KP_d` can be solved by a Las
Vegas algorithm in the same expected time. -/
theorem proposition_5_5 (d : ℕ) (hd : 3 ≤ d) (hBP : BPSolvable d) : KPSolvable d := by sorry

end SoftmaxAttnFD
