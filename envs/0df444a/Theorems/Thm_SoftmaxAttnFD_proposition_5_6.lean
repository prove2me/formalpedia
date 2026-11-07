-- Prove2me | Theorems.Thm_SoftmaxAttnFD_proposition_5_6
-- name    : SoftmaxAttnFD.proposition_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:05:07.135651+00:00
-- url     : https://prove2.me/theorems/f43e33ff-f861-455a-a88b-4be976d3d7c4
-- title:
--   Proposition 5.6, p.22 — from $\mathrm{KP}_{d-1}$ to $\mathrm{BP}_{d-1}$
-- statement:
--   Let $d\ge3$ and suppose a Las Vegas algorithm solves $\mathrm{KP}_{d-1}$ in expected time $\tilde O(F_{d-1}(m,n))$. Then $\mathrm{BP}_{d-1}$ can be solved by a Las Vegas algorithm in expected time $\tilde O(F_d(m,n))$.
--   This is the block-decomposition half of one induction step, where the exponent gains from dimension $d-1$ to the exponent of $F_d$.
--
--   Differences from the source:
--   - encoding: "a Las Vegas algorithm solves … in expected time Õ(·)" → KPSolvable (d − 1) → BPSolvable d, each with its own program, C and K; reason: the page names no machine (Machine), and soft-O has constants fixed before the instance
-- source:
--   Huang, Chen, Softmax Attention with Any Temperature in Fixed Dimension, arXiv:2611.06055 (sha256 a60f7609…), Proposition 5.6, p.22

import Definitions.Def_SoftmaxAttnFD_BiasedProducts

namespace SoftmaxAttnFD

/-- **Proposition 5.6** (arXiv:2611.06055, sha256 a60f7609…, p.22). Let `d ≥ 3` and suppose a Las Vegas
algorithm solves `KP_{d−1}` in expected time `Õ(F_{d−1}(m, n))`. Then `BP_{d−1}` can be solved by a Las
Vegas algorithm in expected time `Õ(F_d(m, n))`. -/
theorem proposition_5_6 (d : ℕ) (hd : 3 ≤ d) (hKP : KPSolvable (d - 1)) : BPSolvable d := by sorry

end SoftmaxAttnFD
