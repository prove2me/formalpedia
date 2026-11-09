-- Prove2me | Theorems.Thm_TusnadyPlane_RandomPoints_lemma_2_1
-- name    : TusnadyPlane.RandomPoints.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:27:53.768793+00:00
-- url     : https://prove2.me/theorems/b60ec604-d7c1-4ba2-94e5-654d711b012d
-- title:
--   Lemma 2.1 — Vertical comparison
-- statement:
--   Let $J=[\ell,u)$ with $\ell<u$, let $b\ge3$ be an integer, and partition $J$ into $b$ equal ordered blocks $B_1,\ldots,B_b$. For every real function $f$ taking finitely many values on $J$,
--   $$b\operatorname{osc}_J f\ge\sum_{k=1}^b\operatorname{osc}_{B_k}f+2|\operatorname{mid}_{B_b}f-\operatorname{mid}_{B_1}f|.$$
--   This deterministic comparison retains both endpoint-block midpoints and applies beyond signed-count functions. It supplies the vertical comparison for local gain.
--
--   Differences from the source:
--   - encoding: finite-valued function on J and blocks numbered 1 through b → a real function with finite image on Set.Ico lo hi and blocks indexed by Fin b; reason: restriction to J and the index shift preserve all functions and every block; the extrema exist on the nonempty finite images
-- source:
--   Zhewei Wei, Tight Bounds for Tusnády’s Problem in the Plane, STOC 2027 submission #313 (October 2026), printed p. 5 (PDF p. 6), Lemma 2.1, (4)

import Mathlib
import Definitions.Def_TusnadyPlane_RandomPoints_oscillation
open MeasureTheory ProbabilityTheory

namespace TusnadyPlane.RandomPoints

/-- Lemma 2.1, printed p.5 / PDF p.6, (4). -/
theorem lemma_2_1 (b : ℕ) (hb : 3 ≤ b) (lo hi : ℝ) (hJ : lo < hi)
    (f : ℝ → ℝ) (hf : (f '' Set.Ico lo hi).Finite) :
    (∑ k : Fin b, oscillation (block lo hi b k.val) f) +
      2 * |midpoint (block lo hi b (b-1)) f - midpoint (block lo hi b 0) f| ≤
        (b : ℝ) * oscillation (Set.Ico lo hi) f := by sorry

end TusnadyPlane.RandomPoints
