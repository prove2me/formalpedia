-- Prove2me | Theorems.Thm_SoftmaxAttnFD_theorem_5_8
-- name    : SoftmaxAttnFD.theorem_5_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:04:03.261726+00:00
-- url     : https://prove2.me/theorems/d1af0118-a247-49e0-9f89-ae8163c9229c
-- title:
--   Theorem 5.8, p.22 — kernel products in fixed dimension
-- statement:
--   For every fixed integer $d\ge2$, a Las Vegas algorithm solves $\mathrm{KP}_d$ in expected time $\tilde O(F_d(m,n))$.
--   It closes the induction on the dimension, and the main theorem follows from it by writing attention as a ratio of kernel products.
--
--   Differences from the source:
--   - encoding: "a Las Vegas algorithm solves KP_d in expected time Õ(F_d(m, n))" → KPSolvable d: one program, C and K before the instance, on the KP layouts; reason: the page names no machine (Machine), and soft-O has constants fixed before the instance
-- source:
--   Huang, Chen, Softmax Attention with Any Temperature in Fixed Dimension, arXiv:2611.06055 (sha256 a60f7609…), Theorem 5.8, p.22

import Definitions.Def_SoftmaxAttnFD_KernelProducts

namespace SoftmaxAttnFD

/-- **Theorem 5.8** (arXiv:2611.06055, sha256 a60f7609…, p.22). For every fixed integer `d ≥ 2`, a Las
Vegas algorithm solves `KP_d` in expected time `Õ(F_d(m, n))`. -/
theorem theorem_5_8 (d : ℕ) (hd : 2 ≤ d) : KPSolvable d := by sorry

end SoftmaxAttnFD
