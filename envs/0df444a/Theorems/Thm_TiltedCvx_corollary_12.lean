-- Prove2me | Theorems.Thm_TiltedCvx_corollary_12
-- name    : TiltedCvx.corollary_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:40:13.43618+00:00
-- url     : https://prove2.me/theorems/d1759102-57ca-48a4-bebf-c501c22104ca
-- title:
--   Corollary 12 — Lebourg's mean value theorem with continuity only at the endpoints
-- statement:
--   Let $K\subseteq\mathbb R^d$ be convex, let $x,y\in K$ be distinct, and let $f:K\to\mathbb R$ be continuous on the closed segment $[x,y]$ and locally Lipschitz on an open set containing the open segment $(x,y)$. Then there are a point $z\in(x,y)$ and a vector
--
--   $$
--   v\in\bar\partial f(z)=\operatorname{conv}\big(\partial f(z)\big)\quad\text{with}\quad f(y)-f(x)=\langle v,y-x\rangle .
--   $$
--
--   Subdifferentials are those of the proper extension of $f$ (equal to $+\infty$ off $K$). This extends Lebourg's theorem, which asks for Lipschitz continuity on a neighbourhood of the closed segment.
--
--   **Formalization Note** $f$ is a real function on $E$ of which only the values on $K$ matter; $\bar\partial f$ and $\partial f$ are the published Clarke and limiting subdifferentials of `properExt K f`. The open set $U$ lies in $K$, the domain of $f$. Both parts of the conclusion, the identity $\bar\partial f(z)=\operatorname{conv}\partial f(z)$ and the mean value, are asserted at the point $z$.
--
--   Differences from the source:
--   - generalization: functions on ℝ^d → functions on a finite-dimensional real inner product space E; reason: every such E is isometric to ℝ^d and ℝ^d = EuclideanSpace ℝ (Fin d) is an instance, so the statement specializes to the paper's
--   - reading: f : K → ℝ locally Lipschitz on an open set containing (x, y) → an open U with (x, y) ⊆ U ⊆ K and LocallyLipschitzOn U f; reason: f is defined only on K, so the open set on which it is locally Lipschitz lies in K
--   - encoding: ∂̄f(z), ∂f(z) of f : K → ℝ → ClarkeSubdiff and LimitingSubdiff of properExt K f; reason: the convention of §3, p.10: subdifferentials refer to the proper extension
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Corollary 12, p.50

import Mathlib
import Definitions.Def_TiltedCvx_properExt
import Definitions.Def_ClarkeStrat_Proj_Setting
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff

open scoped InnerProductSpace
open ClarkeStrat.Proj NonconvexSplitting.Shared

namespace TiltedCvx

/-- **Corollary 12 (Lebourg's mean value theorem with continuity at the endpoints).**
Pedramfar–Khanna–Quinn–Aggarwal, arXiv:2611.03472, Corollary 12, p.50. Let `K ⊆ ℝ^d` be convex,
`x, y ∈ K` distinct, and `f : K → ℝ` continuous on `[x, y]` and locally Lipschitz on an open set
containing `(x, y)`. Then there are `z ∈ (x, y)` and `v ∈ ∂̄f(z) = conv(∂f(z))` with
`f(y) − f(x) = ⟨v, y − x⟩`.

**Formalization Note** `f` is given as a real function on `E` of which only the values on `K`
matter; `∂̄f` and `∂f` are those of the proper extension `f̃` (`+∞` off `K`, §3, p.10), i.e. the
published `ClarkeStrat.Proj.ClarkeSubdiff` and `NonconvexSplitting.Shared.LimitingSubdiff` of
`properExt K f`. The open set `U` lies in `K`, where `f` is defined. Both conclusions are stated
at the point `z`: the identity `∂̄f(z) = conv(∂f(z))` and the mean value. -/
theorem corollary_12 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (K : Set E) (hK : Convex ℝ K) (x y : E) (hx : x ∈ K) (hy : y ∈ K)
    (hxy : x ≠ y) (f : E → ℝ) (hcont : ContinuousOn f (segment ℝ x y)) (U : Set E)
    (hU : IsOpen U) (hsegU : openSegment ℝ x y ⊆ U) (hUK : U ⊆ K)
    (hlip : LocallyLipschitzOn U f) :
    ∃ z ∈ openSegment ℝ x y,
      ClarkeSubdiff (properExt K f) z = convexHull ℝ (LimitingSubdiff (properExt K f) z) ∧
      ∃ v ∈ ClarkeSubdiff (properExt K f) z, f y - f x = ⟪v, y - x⟫_ℝ := by sorry

end TiltedCvx
