-- Prove2me | Theorems.Thm_TiltedCvx_Supplement_theorem_1
-- name    : TiltedCvx.Supplement.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:26:25.397998+00:00
-- url     : https://prove2.me/theorems/878527ae-8cc1-4383-be57-4e8a4650e5d8
-- title:
--   Theorem 1 — convexity through the Clarke subdifferential
-- statement:
--   Let $f:\mathbb R^d\to\overline{\mathbb R}$ be a proper lower semicontinuous function and let $\overline\partial f$ be its Clarke–Rockafellar subdifferential. The following are equivalent:
--
--   1. for all $x,y\in\operatorname{dom}(f)$ and $v\in\overline\partial f(x)$, $\ f(y)-f(x)\ge\langle y-x,v\rangle$;
--   2. $f$ is $1$–tilted convex;
--   3. $f$ is convex;
--   4. the operator $\overline\partial f$ is $1$–tilted monotone;
--   5. the operator $\overline\partial f$ is monotone: $\langle y^*-x^*,y-x\rangle\ge0$ for $x^*\in\overline\partial f(x)$, $y^*\in\overline\partial f(y)$.
--
--   This restates the classical subgradient and monotonicity characterizations of convexity in terms of the tilt $\psi_1=\mathrm{id}$; it identifies the top classes $\mathcal F^1=\mathcal F^1_{\mathrm{mono}}$ with the proper lsc convex functions.
--
--   Differences from the source:
--   - generalization: functions on ℝ^d → functions on a finite-dimensional real inner product space E; reason: every such E is isometric to ℝ^d and ℝ^d = EuclideanSpace ℝ (Fin d) is an instance, so the statement specializes to the paper's
--   - encoding: ℝ̄ = ℝ ∪ {±∞}, dom(f) = {f finite} → EReal and the published TiltedCvx.effDom; reason: Lean convention; same instances
--   - encoding: f : ℝ^d → ℝ̄ is convex → the published epigraph convexity WassersteinDRO.ConvexLossP1.IsConvexExt f (the epigraph {(x, t) : f x ≤ t} is convex); reason: the standard notion for extended-valued functions; Mathlib's ConvexOn needs an ordered-module codomain, which EReal is not
--   - encoding: ∂̄f is monotone → the published AccelPPM.FPR.IsMonotoneOp (ClarkeSubdiff f): ⟨x − y, u − v⟩ ≥ 0 for u ∈ ∂̄f(x), v ∈ ∂̄f(y); reason: the same inequality as ⟨y* − x*, y − x⟩ ≥ 0
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Theorem 1, p.15

import Mathlib
import Definitions.Def_TiltedCvx_effDom
import Definitions.Def_TiltedCvx_IsProper
import Definitions.Def_TiltedCvx_TiltedConvex
import Definitions.Def_TiltedCvx_TiltedMonotone
import Definitions.Def_ClarkeStrat_Proj_Setting
import Definitions.Def_WassersteinDRO_ConvexLossP1_IsConvexExt
import Definitions.Def_AccelPPM_FPR_IsMaximalMonotone

open scoped InnerProductSpace
open ClarkeStrat.Proj

namespace TiltedCvx.Supplement

/-- **Theorem 1 (convexity through the Clarke subdifferential).** Pedramfar–Khanna–Quinn–Aggarwal,
*Tilted Convexity and an Exact Offline–Online Separation*, arXiv:2611.03472, Theorem 1, p.15. Let
`f : ℝ^d → ℝ̄` be a proper lsc function. Then the following are equivalent:
(i) for all `x, y ∈ dom(f)` and `v ∈ ∂̄f(x)`, `f(y) − f(x) ≥ ⟨y − x, v⟩`;
(ii) `f` is 1–tilted convex;
(iii) `f` is convex;
(iv) the operator `∂̄f` is 1–tilted monotone;
(v) the operator `∂̄f` is monotone.

**Formalization Note** `∂̄f` is the published `ClarkeStrat.Proj.ClarkeSubdiff`. Convexity of
`f : E → ℝ̄` is the published epigraph convexity `WassersteinDRO.ConvexLossP1.IsConvexExt`, and
monotonicity of a set-valued operator is the published `AccelPPM.FPR.IsMonotoneOp`
(`⟨x − y, u − v⟩ ≥ 0` for `u ∈ F x`, `v ∈ F y`, the same as `⟨y* − x*, y − x⟩ ≥ 0`). -/
theorem theorem_1 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → EReal) (hf : TiltedCvx.IsProper f)
    (hlsc : LowerSemicontinuous f) :
    List.TFAE
      [∀ x ∈ TiltedCvx.effDom f, ∀ y ∈ TiltedCvx.effDom f, ∀ v ∈ ClarkeSubdiff f x,
          ((⟪y - x, v⟫_ℝ : ℝ) : EReal) ≤ f y - f x,
       TiltedCvx.TiltedConvex 1 f,
       WassersteinDRO.ConvexLossP1.IsConvexExt f,
       TiltedCvx.TiltedMonotone 1 (ClarkeSubdiff f),
       AccelPPM.FPR.IsMonotoneOp (ClarkeSubdiff f)] := by sorry

end TiltedCvx.Supplement
