-- Prove2me | Theorems.Thm_TiltedCvx_Supplement_theorem_2
-- name    : TiltedCvx.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:26:58.007127+00:00
-- url     : https://prove2.me/theorems/bfe80b68-6bb5-4546-9a1b-19d89ba397ac
-- title:
--   Theorem 2 — quasiconvexity through the Clarke subdifferential
-- statement:
--   Let $f:\mathbb R^d\to\overline{\mathbb R}$ be proper, lower semicontinuous and radially continuous. The following are equivalent:
--
--   1. for all $x,y\in\operatorname{dom}(f)$ and $v\in\overline\partial f(x)$ with $\langle y-x,v\rangle>0$, $\ f(y)\ge f(x)$;
--   2. $f$ is $0$–tilted convex;
--   3. $f$ is quasiconvex;
--   4. the operator $\overline\partial f$ is $0$–tilted monotone;
--   5. the operator $\overline\partial f$ is quasimonotone.
--
--   Here $\psi_0(z)=0$ for $z>0$, $-\infty$ for $z<0$, and the defining inequalities are imposed only where $\psi_0$ is defined ($z\ne0$). The theorem identifies the bottom class $\mathcal F^0$ with the quasiconvex functions among radially continuous ones.
--
--   **Formalization Note** $0$–tilted convexity and monotonicity are the published `TiltedConvex 0` and `TiltedMonotone 0`, whose `TiltDefined` clause excludes the undefined value $\psi_0(0)$.
--
--   Differences from the source:
--   - generalization: functions on ℝ^d → functions on a finite-dimensional real inner product space E; reason: every such E is isometric to ℝ^d and ℝ^d = EuclideanSpace ℝ (Fin d) is an instance, so the statement specializes to the paper's
--   - encoding: ℝ̄ = ℝ ∪ {±∞}, dom(f) = {f finite} → EReal and the published TiltedCvx.effDom; reason: Lean convention; same instances
--   - encoding: f is quasiconvex → QuasiconvexOn ℝ Set.univ f (convex sublevel sets); reason: the definition the paper uses, as in the published TiltedCvx.theorem_4
--   - encoding: inequalities imposed whenever ψ₀(⟨·,·⟩) is defined → the published TiltDefined clause (γ ≠ 0 ∨ z ≠ 0); reason: the published encoding of “whenever defined”
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Theorem 2, p.16

import Mathlib
import Definitions.Def_TiltedCvx_effDom
import Definitions.Def_TiltedCvx_IsProper
import Definitions.Def_TiltedCvx_TiltedConvex
import Definitions.Def_TiltedCvx_TiltedMonotone
import Definitions.Def_ClarkeStrat_Proj_Setting
import Definitions.Def_TiltedCvx_Supplement_RadiallyContinuous
import Definitions.Def_TiltedCvx_Supplement_IsQuasimonotone

open scoped InnerProductSpace
open ClarkeStrat.Proj

namespace TiltedCvx.Supplement

/-- **Theorem 2 (quasiconvexity through the Clarke subdifferential).**
Pedramfar–Khanna–Quinn–Aggarwal, arXiv:2611.03472, Theorem 2, p.16. Let `f : ℝ^d → ℝ̄` be a
proper, lsc, and radially continuous function. Then the following are equivalent:
(i) for all `x, y ∈ dom(f)` and `v ∈ ∂̄f(x)` such that `⟨y − x, v⟩ > 0`, `f(y) ≥ f(x)`;
(ii) `f` is 0–tilted convex;
(iii) `f` is quasiconvex;
(iv) the operator `∂̄f` is 0–tilted monotone;
(v) the operator `∂̄f` is quasimonotone.

**Formalization Note** 0–tilted convexity and monotonicity are the published `TiltedConvex 0` and
`TiltedMonotone 0`, whose `TiltDefined` clause drops the undefined case `ψ₀(0)` ("whenever the
right-hand side is well-defined"). Quasiconvexity is Mathlib's `QuasiconvexOn ℝ Set.univ f`
(convex sublevel sets), as in the published `TiltedCvx.theorem_4`. -/
theorem theorem_2 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → EReal) (hf : TiltedCvx.IsProper f)
    (hlsc : LowerSemicontinuous f) (hrad : RadiallyContinuous f) :
    List.TFAE
      [∀ x ∈ TiltedCvx.effDom f, ∀ y ∈ TiltedCvx.effDom f, ∀ v ∈ ClarkeSubdiff f x,
          0 < ⟪y - x, v⟫_ℝ → f x ≤ f y,
       TiltedCvx.TiltedConvex 0 f,
       QuasiconvexOn ℝ Set.univ f,
       TiltedCvx.TiltedMonotone 0 (ClarkeSubdiff f),
       IsQuasimonotone (ClarkeSubdiff f)] := by sorry

end TiltedCvx.Supplement
