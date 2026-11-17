-- Prove2me | Theorems.Thm_TiltedCvx_Supplement_theorem_37
-- name    : TiltedCvx.Supplement.theorem_37
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:38:08.414945+00:00
-- url     : https://prove2.me/theorems/ece28d0b-b1d4-48fa-91f3-f73e9613f722
-- title:
--   Theorem 37 — convex domain and quasiconvexity under Fréchet tilted convexity
-- statement:
--   Let $f:\mathbb R^d\to\overline{\mathbb R}$ be proper, lower semicontinuous and $\gamma$–tilted convex with respect to the Fréchet subdifferential $\hat\partial f$ for some $\gamma\in(0,1]$:
--
--   $$
--   f(y)-f(x)\ge\psi_\gamma(\langle y-x,v\rangle)\qquad(x,y\in\operatorname{dom}(f),\ v\in\hat\partial f(x)).
--   $$
--
--   Then $\operatorname{dom}(f)$ is convex and $f$ is quasiconvex.
--
--   Since $\hat\partial f\subseteq\overline\partial f$, this is a slightly stronger version of Theorem 4.
--
--   Differences from the source:
--   - generalization: functions on ℝ^d → functions on a finite-dimensional real inner product space E; reason: every such E is isometric to ℝ^d and ℝ^d = EuclideanSpace ℝ (Fin d) is an instance, so the statement specializes to the paper's
--   - encoding: ℝ̄ = ℝ ∪ {±∞}, dom(f) = {f finite} → EReal and the published TiltedCvx.effDom; reason: Lean convention; same instances
--   - encoding: f is quasiconvex → QuasiconvexOn ℝ Set.univ f (convex sublevel sets); reason: the definition the paper uses, as in the published TiltedCvx.theorem_4
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Theorem 37, p.60

import Mathlib
import Definitions.Def_TiltedCvx_effDom
import Definitions.Def_TiltedCvx_IsProper
import Definitions.Def_TiltedCvx_TiltedConvexWrt
import Definitions.Def_NAPPAL_VPEB_frechetSubdiff

open NAPPAL.VPEB

namespace TiltedCvx.Supplement

/-- **Theorem 37 (Theorem 4 under Fréchet tilted convexity).** Pedramfar–Khanna–Quinn–Aggarwal,
arXiv:2611.03472, Theorem 37, p.60. Let `f : ℝ^d → ℝ̄` be proper, lsc, and γ–tilted convex with
respect to `∂̂f` for some `γ ∈ (0, 1]`. Then `dom(f)` is convex and `f` is quasiconvex.

**Formalization Note** `∂̂f` is the published `NAPPAL.VPEB.frechetSubdiff`; the hypothesis is the
published `TiltedConvexWrt γ f (frechetSubdiff f)`, weaker than Clarke tilted convexity (the
published `TiltedCvx.theorem_4`). Quasiconvexity is `QuasiconvexOn ℝ Set.univ f`, as in
`theorem_4`. -/
theorem theorem_37 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (f : E → EReal)
    (hf : TiltedCvx.IsProper f) (hlsc : LowerSemicontinuous f)
    (htc : TiltedCvx.TiltedConvexWrt γ f (frechetSubdiff f)) :
    Convex ℝ (TiltedCvx.effDom f) ∧ QuasiconvexOn ℝ Set.univ f := by sorry

end TiltedCvx.Supplement
