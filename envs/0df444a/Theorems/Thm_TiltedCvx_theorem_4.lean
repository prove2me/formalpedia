-- Prove2me | Theorems.Thm_TiltedCvx_theorem_4
-- name    : TiltedCvx.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:42:07.645564+00:00
-- url     : https://prove2.me/theorems/75e337de-bfc7-4d05-a30f-eae1b530b077
-- title:
--   Theorem 4 — tilted convex functions have convex domains and are quasiconvex
-- statement:
--   Let $f:\mathbb R^d\to\overline{\mathbb R}$ be proper, lower semicontinuous and $\gamma$–tilted convex for some $\gamma\in(0,1]$. Then $\operatorname{dom}(f)$ is convex and $f$ is quasiconvex:
--
--   $$
--   \operatorname{dom}(f)\ \text{convex},\qquad f(\lambda x+(1-\lambda)y)\le\max\{f(x),f(y)\}\quad(\lambda\in[0,1]).
--   $$
--
--   Convexity of the domain is thus a consequence of tilted convexity rather than an assumption.
--
--   **Formalization Note** Quasiconvexity is `QuasiconvexOn ℝ Set.univ f`: every sublevel set $\{x : f(x)\le r\}$, $r\in\overline{\mathbb R}$, is convex.
--
--   Differences from the source:
--   - generalization: functions on ℝ^d → functions on a finite-dimensional real inner product space E; reason: every such E is isometric to ℝ^d and ℝ^d = EuclideanSpace ℝ (Fin d) is an instance, so the statement specializes to the paper's
--   - encoding: f is quasiconvex → QuasiconvexOn ℝ Set.univ f (convex sublevel sets); reason: the definition the paper uses (p.1)
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Theorem 4, p.18

import Mathlib
import Definitions.Def_TiltedCvx_effDom
import Definitions.Def_TiltedCvx_IsProper
import Definitions.Def_TiltedCvx_TiltedConvex

namespace TiltedCvx

/-- **Theorem 4 (convex domain and quasiconvexity).** Pedramfar–Khanna–Quinn–Aggarwal,
arXiv:2611.03472, Theorem 4, p.18. Let `f : ℝ^d → ℝ̄` be proper, lsc, and γ–tilted convex for
some `γ ∈ (0, 1]`. Then `dom(f)` is convex and `f` is quasiconvex.

**Formalization Note** Quasiconvexity is Mathlib's `QuasiconvexOn ℝ Set.univ f`: every sublevel
set `{x | f x ≤ r}`, `r ∈ ℝ̄`, is convex (p.1). -/
theorem theorem_4 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (f : E → EReal)
    (hf : IsProper f) (hlsc : LowerSemicontinuous f) (htc : TiltedConvex γ f) :
    Convex ℝ (effDom f) ∧ QuasiconvexOn ℝ Set.univ f := by sorry

end TiltedCvx
