-- Prove2me | Theorems.Thm_SampleCRS_AlmostGreedy_Supplement_lemma_b_2
-- name    : SampleCRS.AlmostGreedy.Supplement.lemma_b_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:44:55.593459+00:00
-- url     : https://prove2.me/theorems/f44aa251-9bd5-4b34-ae0c-0cdd26b386bb
-- title:
--   Lemma B.2 — reciprocal Poisson acceptance is convex
-- statement:
--   For every integer $k\ge2$, define $F_k(\lambda)=1/E[\operatorname{AR}_k(\operatorname{Poi}(\lambda))]$. Then
--   $$F_k\text{ is convex on the entire real interval }[k-1,k].$$
--   Equivalently, $u\mapsto F_k(k-u)$ is convex on $[0,1]$. The parameter is real, not restricted to integer means, and both endpoints are included. This supplies the interpolation inequality used for Conservative Scaling.
--
--   Differences from the source:
--   - encoding: Poisson parameter λ∈[k−1,k] → Real.toNNReal λ in the published bounded-test Poisson expectation; reason: λ≥0 on the entire claimed interval, so this conversion does not change any parameter or expectation
-- source:
--   Shaddin Dughmi, Vasilis Livanos, Pranav Nuti, STOC 2027 submission #686 (October 2026), Lemma B.2, p. 42

import Mathlib
import Definitions.Def_SampleCRS_AlmostGreedy_Supplement_scaling

namespace SampleCRS.AlmostGreedy.Supplement

/-- Lemma B.2, p.42. reciprocal Poisson acceptance is convex. -/
theorem lemma_b_2 (k : ℕ) (hk : 2 ≤ k) :
    ConvexOn ℝ (Set.Icc ((k : ℝ) - 1) (k : ℝ)) (reciprocalAR k) := by sorry

end SampleCRS.AlmostGreedy.Supplement
