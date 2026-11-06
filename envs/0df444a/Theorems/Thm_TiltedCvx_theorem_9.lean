-- Prove2me | Theorems.Thm_TiltedCvx_theorem_9
-- name    : TiltedCvx.theorem_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:42:14.176479+00:00
-- url     : https://prove2.me/theorems/2a4a4f08-4484-4d1f-b65f-58cd2ac438dd
-- title:
--   Theorem 9 — $\gamma$-tilted convexity is a property of lines
-- statement:
--   Let $\gamma\in(0,1]$ and let $f:\mathbb R^d\to\overline{\mathbb R}$ be proper and lower semicontinuous. Then $f$ is $\gamma$–tilted convex if and only if, for every line $\ell$ that intersects $\operatorname{dom}(f)$, the restriction
--
--   $$
--   f|_\ell:\ell\to\overline{\mathbb R}
--   $$
--
--   is $\gamma$–tilted convex, where $\ell$ is regarded as a one-dimensional Euclidean space.
--
--   As for convexity, the property can be checked on lines.
--
--   **Formalization Note** A line is $\{x+te\}$ with $\|e\|=1$, and $f|_\ell$ is the function $t\mapsto f(x+te)$ on $\mathbb R$ (`lineRestrict f x e Set.univ`).
--
--   Differences from the source:
--   - generalization: functions on ℝ^d → functions on a finite-dimensional real inner product space E; reason: every such E is isometric to ℝ^d and ℝ^d = EuclideanSpace ℝ (Fin d) is an instance, so the statement specializes to the paper's
--   - encoding: line ℓ regarded as a one-dimensional Euclidean space → ℝ via the unit-speed parametrization t ↦ x + t e, ‖e‖ = 1; reason: an isometry onto ℓ, as in the proof of Corollary 2 (p.21)
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Theorem 9, p.20

import Mathlib
import Definitions.Def_TiltedCvx_effDom
import Definitions.Def_TiltedCvx_IsProper
import Definitions.Def_TiltedCvx_TiltedConvex
import Definitions.Def_TiltedCvx_lineRestrict

namespace TiltedCvx

/-- **Theorem 9 (γ–tilted convexity on lines).** Pedramfar–Khanna–Quinn–Aggarwal,
arXiv:2611.03472, Theorem 9, p.20. Let `γ ∈ (0, 1]` and let `f : ℝ^d → ℝ̄` be proper lsc. Then
`f` is γ–tilted convex if and only if, for every line `ℓ` that intersects `dom(f)`, the
restriction `f|ℓ : ℓ → ℝ̄` is γ–tilted convex, where `ℓ` is regarded as a one-dimensional
Euclidean space.

**Formalization Note** A line is `{x + t e : t ∈ ℝ}` with `‖e‖ = 1`; it meets `dom f` when some
`x + t e ∈ dom f`. Its unit-speed parametrization `t ↦ x + t e` is an isometry of `ℝ` onto `ℓ`
(proof of Corollary 2, p.21), so `f|ℓ` is the function `lineRestrict f x e Set.univ : ℝ → ℝ̄`,
`t ↦ f (x + t e)`. -/
theorem theorem_9 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (f : E → EReal)
    (hf : IsProper f) (hlsc : LowerSemicontinuous f) :
    TiltedConvex γ f ↔
      ∀ x e : E, ‖e‖ = 1 → (∃ t : ℝ, x + t • e ∈ effDom f) →
        TiltedConvex γ (lineRestrict f x e Set.univ) := by sorry

end TiltedCvx
