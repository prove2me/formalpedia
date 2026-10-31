-- Prove2me | Theorems.Thm_SpiderDiameter_lemma_4_1
-- name    : SpiderDiameter.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:38:49.750481+00:00
-- url     : https://prove2.me/theorems/e621bca1-f22b-4c47-8113-354c4c782580
-- title:
--   Lemma 4.1 (corrected $U$: Corollary 3.5 integrand $\varphi(s-1/2)$): majorization $U\ge y-z-x^2$
-- statement:
--   Let $n\ge3$ and let $U$ be the explicit candidate of Section 3. For every $(x,y,z)$ in the state space $\mathcal D$,
--   $$U(x,y,z)\ge y-z-x^2 .$$
--
--   The candidate dominates the gain $G$; together with the supermartingale argument of Lemma 4.2 this gives $\mathbb U\le U$.
--
--   Differences from the source:
--   - reading: "for all (x, y, z)" → for all (x, y, z) in the state space D; reason: D is the state space of p.11 on which U is constructed and the process lives
--   - correction: U built with the printed Corollary 3.5 (integrand denominator (n − 1)s − φ(y − 1/2)) → the candidate U uses the corrected denominator (n − 1)s − φ(s − 1/2) on {y ≥ 1/2, z > φ(y − 1/2)} and in U(1/2, 1/2, s); reason: the printed Corollary 3.5 contradicts Lemma 3.4 and continuity of U across y = 1/2 (n = 3, (x, z) = (−0.05, −0.1): 0.94325 from (3.12) vs 0.97892 printed); see Corollary 3.5
--   - reading: U of Section 3 (from Step 7 on, the strategy value) → the explicit function glued from (3.8), Corollary 3.5 and (3.12)–(3.13), with φ^{−1} the two-branch f: f(z) = z + 1/2 for z ≤ −1/2, and the unique s ≥ 0 with φ(s) = z for z > −1/2; reason: Section 4 treats "the function U constructed in the previous section" and Remark 3.7 compares lines of (3.8); Corollaries 3.3, 3.5 and 3.6 identify that function with the strategy value
-- source:
--   Bednarz–Ernst–Osękowski, On the Diameter of the Stopped Spider Process, arXiv:2105.15202v2, Lemma 4.1, p.18

import Mathlib
import Definitions.Def_SpiderDiameter_Candidate
import Definitions.Def_SpiderDiameter_GeneralProcess

namespace SpiderDiameter

/-- **Lemma 4.1 (majorization)** (Bednarz–Ernst–Osękowski, arXiv:2105.15202v2, Lemma 4.1, p.18):
"We have U(x, y, z) ≥ y − z − x² for all (x, y, z)."

For every `n ≥ 3` and every `(x, y, z)` in the state space `𝒟`, the explicit candidate satisfies
`U(x, y, z) ≥ y − z − x²`.

**Formalization Note (reading).** "for all (x, y, z)" ranges over the state space `𝒟` of p.11,
the domain on which `U` is defined in §3. -/
theorem lemma_4_1 (n : ℕ) (hn : 3 ≤ n) (x y z : ℝ) (hD : (x, y, z) ∈ stateSpace) :
    y - z - x ^ 2 ≤ candidate n x y z := by sorry

end SpiderDiameter
