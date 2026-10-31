-- Prove2me | Theorems.Thm_SpiderDiameter_remark_3_7
-- name    : SpiderDiameter.remark_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:36:53.135402+00:00
-- url     : https://prove2.me/theorems/ea610bd8-5bcb-4aac-a512-806abfa54186
-- title:
--   Remark 3.7 (corrected $U$: Corollary 3.5 integrand $\varphi(s-1/2)$): $U(-y,y,-y)=U(y,y,-y)$
-- statement:
--   Let $n\ge3$ and let $U$ be the explicit candidate of Section 3. For every $y>0$,
--   $$U(-y,y,-y)=U(y,y,-y).$$
--
--   The two states correspond to the same configuration of the spider (the second longest rib has just become the longest), so the symmetry is what makes the jumps of $X$ from $-Y$ to $Y$ invisible in the verification argument of Lemma 4.2.
--
--   Differences from the source:
--   - correction: U built with the printed Corollary 3.5 (integrand denominator (n − 1)s − φ(y − 1/2)) → the candidate U uses the corrected denominator (n − 1)s − φ(s − 1/2) on {y ≥ 1/2, z > φ(y − 1/2)} and in U(1/2, 1/2, s); reason: the printed Corollary 3.5 contradicts Lemma 3.4 and continuity of U across y = 1/2 (n = 3, (x, z) = (−0.05, −0.1): 0.94325 from (3.12) vs 0.97892 printed); see Corollary 3.5
--   - reading: U of Section 3 (from Step 7 on, the strategy value) → the explicit function glued from (3.8), Corollary 3.5 and (3.12)–(3.13), with φ^{−1} the two-branch f: f(z) = z + 1/2 for z ≤ −1/2, and the unique s ≥ 0 with φ(s) = z for z > −1/2; reason: Section 4 treats "the function U constructed in the previous section" and Remark 3.7 compares lines of (3.8); Corollaries 3.3, 3.5 and 3.6 identify that function with the strategy value
-- source:
--   Bednarz–Ernst–Osękowski, On the Diameter of the Stopped Spider Process, arXiv:2105.15202v2, Remark 3.7, p.18

import Mathlib
import Definitions.Def_SpiderDiameter_Candidate

namespace SpiderDiameter

/-- **Remark 3.7 (symmetry at the jump)** (Bednarz–Ernst–Osękowski, arXiv:2105.15202v2,
Remark 3.7, p.18): "It is straightforward to check that, for all y > 0, the function U satisfies
the symmetry condition U(−y, y, −y) = U(y, y, −y): compare the first and the fifth line in (3.8),
see also (3.12) and (3.13)."

For every `n ≥ 3` and every `y > 0`, the explicit candidate satisfies
`U(−y, y, −y) = U(y, y, −y)`. -/
theorem remark_3_7 (n : ℕ) (hn : 3 ≤ n) (y : ℝ) (hy : 0 < y) :
    candidate n (-y) y (-y) = candidate n y y (-y) := by sorry

end SpiderDiameter
