-- Prove2me | Theorems.Thm_TiltedCvx_Supplement_theorem_24
-- name    : TiltedCvx.Supplement.theorem_24
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:34:48.152482+00:00
-- url     : https://prove2.me/theorems/d6f62fbc-a496-4f94-bcf5-b64fb678e791
-- title:
--   Theorem 24 — $H_\gamma$–convex $\iff$ $\gamma^2$–tilted secant convex
-- statement:
--   Let $f:\mathbb R^d\to\overline{\mathbb R}$ be proper and lower semicontinuous and $\gamma\in(0,1]$. Then
--
--   $$
--   f\ \text{is }H_\gamma\text{–convex}\iff f\ \text{is }\gamma^2\text{–tilted secant convex},
--   $$
--
--   where $H_\gamma=\{y\mapsto c+\psi_\gamma(\langle y-w,z\rangle)\}$ is the tilted affine family and $H_\gamma$–convex means a pointwise supremum of a non-empty subfamily.
--
--   Tilted affine functions play for $\gamma^2$–tilted secant convexity the role affine functions play for convexity.
--
--   Differences from the source:
--   - generalization: functions on ℝ^d → functions on a finite-dimensional real inner product space E; reason: every such E is isometric to ℝ^d and ℝ^d = EuclideanSpace ℝ (Fin d) is an instance, so the statement specializes to the paper's
--   - encoding: ℝ̄ = ℝ ∪ {±∞}, dom(f) = {f finite} → EReal and the published TiltedCvx.effDom; reason: Lean convention; same instances
--   - encoding: H_γ–convex (Definitions 7–8) → IsHConvex (tiltedAffine γ) f, supremum in EReal; reason: the paper's definition
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Theorem 24, p.28

import Mathlib
import Definitions.Def_TiltedCvx_IsProper
import Definitions.Def_TiltedCvx_TiltedSecant
import Definitions.Def_TiltedCvx_Supplement_IsHConvex
import Definitions.Def_TiltedCvx_Supplement_tiltedAffine

namespace TiltedCvx.Supplement

/-- **Theorem 24 (envelopes of tilted affine functions).** Pedramfar–Khanna–Quinn–Aggarwal,
arXiv:2611.03472, Theorem 24, p.28. Let `f : ℝ^d → ℝ̄` be a proper lsc function and let
`γ ∈ (0, 1]`. Then `f` is `H_γ`–convex if and only if it is γ²–tilted secant convex.

**Formalization Note** `H_γ`–convexity (Definitions 7–8) is `IsHConvex (tiltedAffine γ) f`: `f` is
the pointwise supremum, in `EReal`, of a non-empty subfamily of `H_γ`. The secant parameter is
`γ ^ 2`. -/
theorem theorem_24 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → EReal) (hf : TiltedCvx.IsProper f)
    (hlsc : LowerSemicontinuous f) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) :
    IsHConvex (tiltedAffine γ) f ↔ TiltedCvx.TiltedSecant (γ ^ 2) f := by sorry

end TiltedCvx.Supplement
