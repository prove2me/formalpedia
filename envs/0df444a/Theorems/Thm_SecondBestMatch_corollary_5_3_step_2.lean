-- Prove2me | Theorems.Thm_SecondBestMatch_corollary_5_3_step_2
-- name    : SecondBestMatch.corollary_5_3_step_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:18:37.739642+00:00
-- url     : https://prove2.me/theorems/7f57fab7-e067-4352-a8ee-4b6398acdae4
-- title:
--   Proof of Corollary 5.3, Step 2 — $\alpha\mapsto g_\alpha$ is strictly decreasing and strictly convex, with limit $1/2$
-- statement:
--   On $[0,\infty)$ the map $\alpha\mapsto g_\alpha = (1+\alpha)/\mathrm B\big(\tfrac1{1+\alpha},\tfrac1{1+\alpha}\big)$
--
--   1. is strictly decreasing and strictly convex;
--   2. is differentiable, and its derivative $g'_\alpha$ is continuous and strictly increasing on $[0,\infty)$ and maps $[0,\infty)$ bijectively onto $[-1,0)$;
--   3. decreases strictly to $1/2$:
--   $$
--   \lim_{\alpha\to\infty}g_\alpha = \tfrac12 .
--   $$
--
--   In particular the half-efficiency bound of Theorem 4.10 cannot be improved by choosing a single multiplier: every $g_\alpha$ exceeds $1/2$ but they approach it.
--
--   Differences from the source:
--   - encoding: $g'$ maps $[0,\infty)$ bijectively onto $[-1,0)$ → `StrictMonoOn (deriv gCoeff) (Ici 0)` and `deriv gCoeff '' Ici 0 = Ico (-1) 0`, with differentiability at every $\alpha\ge0$; reason: a strictly increasing map is injective; the image equation is surjectivity
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), proof of Corollary 5.3, Step 2, p.40

import Mathlib
import Definitions.Def_SecondBestMatch_gCoeff

open Set Filter Topology

namespace SecondBestMatch

/-- **Step 2 of the proof of Corollary 5.3** (Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), App. G, p.40): `α ↦ g_α` is strictly
decreasing and strictly convex on `[0, ∞)`. Its derivative `α ↦ g'_α` is continuous and strictly
increasing on `[0, ∞)` and maps `[0, ∞)` bijectively onto `[−1, 0)`, and `g_α` decreases strictly to
`χ(0) = 1/2` as `α → ∞`.

**Formalization Note** `g` is differentiable at every `α ≥ 0` (two-sided: `g_α` is defined by the
same formula for `α > −1`), so `deriv gCoeff` is the paper's `g'` on `[0, ∞)`; "bijectively onto
`[−1, 0)`" is strict monotonicity together with the image `deriv gCoeff '' [0, ∞) = [−1, 0)`. -/
theorem corollary_5_3_step_2 :
    StrictAntiOn gCoeff (Ici 0) ∧ StrictConvexOn ℝ (Ici 0) gCoeff ∧
      (∀ α : ℝ, 0 ≤ α → DifferentiableAt ℝ gCoeff α) ∧
      ContinuousOn (deriv gCoeff) (Ici 0) ∧ StrictMonoOn (deriv gCoeff) (Ici 0) ∧
      deriv gCoeff '' Ici 0 = Ico (-1) 0 ∧
      Tendsto gCoeff atTop (𝓝 (1 / 2)) := by sorry

end SecondBestMatch
