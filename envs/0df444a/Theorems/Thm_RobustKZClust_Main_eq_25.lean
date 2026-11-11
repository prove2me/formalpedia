-- Prove2me | Theorems.Thm_RobustKZClust_Main_eq_25
-- name    : RobustKZClust.Main.eq_25
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:11:40.627202+00:00
-- url     : https://prove2.me/theorems/bff2ab2b-3826-4e53-bc6f-7acb6de94571
-- title:
--   §4.1, Eq. (25) — β_z(t) = (1/z!) Σ_{j=0}^{z+1} (−1)^j C(z+1, j) (t − j)_+^z
-- statement:
--   Let $z\ge1$ be an integer and $V_1,\dots,V_z$ independent and uniform on $[0,1)$. For every $t\in\mathbb R$,
--
--   $$\beta_z(t)=\Pr\Bigl[t-1<\sum_{j=1}^zV_j\le t\Bigr]=\frac1{z!}\sum_{j=0}^{z+1}(-1)^j\binom{z+1}{j}(t-j)_+^z,\qquad u_+=\max\{u,0\}.$$
--
--   This closed form lets the hierarchical assignment's entries $F_\ell(s_\ell v,x)=\beta_z(x/s_\ell-v)$ be evaluated with $O(z^2)$ arithmetic operations in small space.
--
--   Differences from the source:
--   - encoding: Pr over V_1, …, V_z → Lebesgue measure restricted to [0,1)^z; reason: the law of independent uniforms.
-- source:
--   Guo, Jiang, Krauthgamer, Xie, Zhou, Adversarially Robust Streaming Algorithms for (k, z)-Clustering, STOC 2027 submission (manuscript sha256 7d9aadba…), p. 18, §4.1, Eq. (25)

import Mathlib
import Definitions.Def_RobustKZClust_Main_Spline

namespace RobustKZClust.Main

/-- §4.1, Eq. (25) (p. 18): `β_z(t) = (1/z!) ∑_{j=0}^{z+1} (−1)^j C(z+1, j) (t − j)_+^z`. -/
theorem eq_25 (z : ℕ) (hz : 1 ≤ z) (t : ℝ) :
    beta z t = (1 / (z.factorial : ℝ)) *
      ∑ j ∈ Finset.range (z + 2), (-1 : ℝ) ^ j * ((z + 1).choose j : ℝ) * (max (t - j) 0) ^ z := by sorry

end RobustKZClust.Main
