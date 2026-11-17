-- Prove2me | Theorems.Thm_TiltedCvx_Supplement_theorem_15
-- name    : TiltedCvx.Supplement.theorem_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:31:58.210597+00:00
-- url     : https://prove2.me/theorems/5ebbeae7-2b58-455b-8525-b9f47305cc8b
-- title:
--   Theorem 15 — five equivalent forms of γ–tilted monotonicity
-- statement:
--   Let $f:\mathbb R^d\to\overline{\mathbb R}$ be proper and lower semicontinuous with $K:=\operatorname{dom}(f)$, and $\gamma\in(0,1]$. The following are equivalent:
--
--   1. $\overline\partial f$ (Clarke) is $\gamma$–tilted monotone;
--   2. $\partial f$ (limiting) is $\gamma$–tilted monotone;
--   3. $\hat\partial f$ (Fréchet) is $\gamma$–tilted monotone;
--   4. $K$ is convex, $f$ is radially continuous, $f|_{\operatorname{ri}(K)}$ is locally Lipschitz, and $\hat\partial f|_{\operatorname{ri}(K)}$ is $\gamma$–tilted monotone;
--   5. $K$ is convex, $f$ is radially continuous, $f|_{\operatorname{ri}(K)}$ is locally Lipschitz, and $x\mapsto\{\nabla f(x)\}$ on $\operatorname{ri}(K)$ is $\gamma$–tilted monotone:
--   $$
--   \langle\nabla f(y),y-x\rangle\ \ge\ \psi_\gamma\big(\langle\nabla f(x),y-x\rangle\big)
--   $$
--   for all $x,y\in\operatorname{ri}(K)$ where $\nabla f(x)$ and $\nabla f(y)$ exist, the gradient taken with respect to the affine hull of $K$.
--
--   The class $\mathcal F^\gamma_{\mathrm{mono}}$ can therefore be tested with any of the three subdifferentials, or with relative gradients on the relative interior.
--
--   **Formalization Note** $\hat\partial f|_{\operatorname{ri}(K)}$ is the operator equal to $\hat\partial f(x)$ for $x\in\operatorname{ri}(K)$ and empty elsewhere. $\nabla f(x)$ is any $g$ with the published `IsRelGrad f K x g`.
--
--   Differences from the source:
--   - generalization: functions on ℝ^d → functions on a finite-dimensional real inner product space E; reason: every such E is isometric to ℝ^d and ℝ^d = EuclideanSpace ℝ (Fin d) is an instance, so the statement specializes to the paper's
--   - encoding: ℝ̄ = ℝ ∪ {±∞}, dom(f) = {f finite} → EReal and the published TiltedCvx.effDom; reason: Lean convention; same instances
--   - encoding: f|ri(K) is locally Lipschitz → LocallyLipschitzOn (ri K) of x ↦ (f x).toReal, ri K = intrinsicInterior ℝ K; reason: f is finite on ri(K) ⊆ dom f, so toReal reads its values; same condition
--   - encoding: ∂̂f|ri(K) → x ↦ {v | x ∈ ri K ∧ v ∈ ∂̂f(x)}; reason: the restriction of the operator to ri(K), empty elsewhere
--   - encoding: ∇f(x) w.r.t. aff(K), where it exists → any g with the published IsRelGrad f K x g; reason: the published relative-gradient predicate; such g is unique
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Theorem 15, p.23

import Mathlib
import Definitions.Def_TiltedCvx_effDom
import Definitions.Def_TiltedCvx_IsProper
import Definitions.Def_TiltedCvx_psi
import Definitions.Def_TiltedCvx_TiltedMonotone
import Definitions.Def_TiltedCvx_IsRelGrad
import Definitions.Def_ClarkeStrat_Proj_Setting
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NAPPAL_VPEB_frechetSubdiff
import Definitions.Def_TiltedCvx_Supplement_RadiallyContinuous

open scoped InnerProductSpace
open ClarkeStrat.Proj NonconvexSplitting.Shared NAPPAL.VPEB

namespace TiltedCvx.Supplement

/-- **Theorem 15 (five equivalent forms of γ–tilted monotonicity).**
Pedramfar–Khanna–Quinn–Aggarwal, arXiv:2611.03472, Theorem 15, p.23. Assume `f : ℝ^d → ℝ̄` is a
proper lsc function with effective domain `K := dom(f)` and `γ ∈ (0, 1]`. Then the following are
equivalent:
(i) `∂̄f` is γ–tilted monotone;
(ii) `∂f` is γ–tilted monotone;
(iii) `∂̂f` is γ–tilted monotone;
(iv) `K` is convex, `f` is radially continuous, `f|ri(K)` is locally Lipschitz, and `∂̂f|ri(K)`
is γ–tilted monotone;
(v) `K` is convex, `f` is radially continuous, `f|ri(K)` is locally Lipschitz, and
`x ↦ {∇f(x)} : ri(K) ⇒ ℝ^d` is γ–tilted monotone, i.e. `⟨∇f(y), y − x⟩ ≥ ψγ(⟨∇f(x), y − x⟩)` for
all `x, y ∈ ri(K)` where `∇f(x)` and `∇f(y)` exist, `∇f` taken with respect to `aff(K)`.

**Formalization Note** `∂̄f`, `∂f`, `∂̂f` are the published `ClarkeSubdiff`, `LimitingSubdiff`
and `frechetSubdiff`. `∂̂f|ri(K)` is the operator equal to `∂̂f(x)` for `x ∈ ri(K)` and `∅`
elsewhere. "`f|ri(K)` locally Lipschitz" is `LocallyLipschitzOn (ri K)` of `x ↦ (f x).toReal`
(finite there). `∇f(x)` is any `g` with the published `IsRelGrad f K x g`. For `γ > 0` every tilt
is defined. -/
theorem theorem_15 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (f : E → EReal)
    (hf : TiltedCvx.IsProper f) (hlsc : LowerSemicontinuous f) :
    List.TFAE
      [TiltedCvx.TiltedMonotone γ (ClarkeSubdiff f),
       TiltedCvx.TiltedMonotone γ (LimitingSubdiff f),
       TiltedCvx.TiltedMonotone γ (frechetSubdiff f),
       Convex ℝ (TiltedCvx.effDom f) ∧ RadiallyContinuous f ∧
         LocallyLipschitzOn (intrinsicInterior ℝ (TiltedCvx.effDom f))
           (fun x => (f x).toReal) ∧
         TiltedCvx.TiltedMonotone γ
           (fun x => {v | x ∈ intrinsicInterior ℝ (TiltedCvx.effDom f) ∧
             v ∈ frechetSubdiff f x}),
       Convex ℝ (TiltedCvx.effDom f) ∧ RadiallyContinuous f ∧
         LocallyLipschitzOn (intrinsicInterior ℝ (TiltedCvx.effDom f))
           (fun x => (f x).toReal) ∧
         ∀ x ∈ intrinsicInterior ℝ (TiltedCvx.effDom f),
           ∀ y ∈ intrinsicInterior ℝ (TiltedCvx.effDom f), ∀ gx gy : E,
             TiltedCvx.IsRelGrad f (TiltedCvx.effDom f) x gx →
             TiltedCvx.IsRelGrad f (TiltedCvx.effDom f) y gy →
               TiltedCvx.psi γ ((⟪gx, y - x⟫_ℝ : ℝ) : EReal) ≤ ((⟪gy, y - x⟫_ℝ : ℝ) : EReal)]
    := by sorry

end TiltedCvx.Supplement
