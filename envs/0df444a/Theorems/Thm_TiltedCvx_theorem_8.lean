-- Prove2me | Theorems.Thm_TiltedCvx_theorem_8
-- name    : TiltedCvx.theorem_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:42:18.986233+00:00
-- url     : https://prove2.me/theorems/ba511d06-c8c8-413e-9620-8e58346d791b
-- title:
--   Theorem 8 — five equivalent forms of $\gamma$-tilted convexity
-- statement:
--   Let $\gamma\in(0,1]$ and let $f:\mathbb R^d\to\overline{\mathbb R}$ be proper and lower semicontinuous, with $K:=\operatorname{dom}(f)$. The following are equivalent.
--
--   1. $f$ is $\gamma$–tilted convex (with respect to the Clarke subdifferential $\bar\partial f$).
--   2. $f$ is $\gamma$–tilted convex with respect to the limiting subdifferential $\partial f$.
--   3. $f$ is $\gamma$–tilted convex with respect to the Fréchet subdifferential $\hat\partial f$.
--   4. $K$ is convex and $f(y)-f(x)\ge\psi_\gamma(\langle v,y-x\rangle)$ for all $y\in K$, $x\in\operatorname{ri}(K)$ and $v\in\hat\partial f(x)$.
--   5. $K$ is convex, the points $x\in\operatorname{ri}(K)$ where $\nabla f(x)$ exists are dense in $K$, and
--   $$
--   f(y)-f(x)\ge\psi_\gamma\big(\langle\nabla f(x),y-x\rangle\big)
--   $$
--   for all $y\in K$ and all $x\in\operatorname{ri}(K)$ where $\nabla f(x)$ exists; here $\nabla f(x)$ is the gradient with respect to the affine hull of $K$.
--
--   So tilted convexity does not depend on the choice of subdifferential, and it can be tested with gradients alone.
--
--   **Formalization Note** $\operatorname{ri}(K)$ is `intrinsicInterior ℝ K`; "dense in $K$" is $K\subseteq\overline S$; $\nabla f(x)$ is any $g$ with `IsRelGrad f K x g` (such $g$ is unique). For $\gamma>0$ every tilt is defined.
--
--   Differences from the source:
--   - generalization: functions on ℝ^d → functions on a finite-dimensional real inner product space E; reason: every such E is isometric to ℝ^d and ℝ^d = EuclideanSpace ℝ (Fin d) is an instance, so the statement specializes to the paper's
--   - encoding: ∇f(x) exists, gradient with respect to aff(K) → ∀ g with IsRelGrad f K x g (derivative within affineSpan ℝ K, g in its direction); reason: the relative gradient is unique when it exists; same instances
--   - encoding: the set … is dense in K → K ⊆ closure S; reason: definition of density of S in K
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Theorem 8, pp.19–20

import Mathlib
import Definitions.Def_TiltedCvx_effDom
import Definitions.Def_TiltedCvx_IsProper
import Definitions.Def_TiltedCvx_psi
import Definitions.Def_NAPPAL_VPEB_frechetSubdiff
import Definitions.Def_TiltedCvx_TiltedConvexWrt
import Definitions.Def_TiltedCvx_TiltedConvex
import Definitions.Def_TiltedCvx_IsRelGrad
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff

open scoped InnerProductSpace
open NonconvexSplitting.Shared
open NAPPAL.VPEB

namespace TiltedCvx

/-- **Theorem 8 (five equivalent forms of γ–tilted convexity).** Pedramfar–Khanna–Quinn–Aggarwal,
arXiv:2611.03472, Theorem 8, pp.19–20. Let `γ ∈ (0, 1]` and let `f : ℝ^d → ℝ̄` be proper lsc with
`K := dom(f)`. The following are equivalent:
(i) `f` is γ–tilted convex;
(ii) `f` is γ–tilted convex with respect to the limiting subdifferential `∂f`;
(iii) `f` is γ–tilted convex with respect to the Fréchet subdifferential `∂̂f`;
(iv) `K` is convex and `f(y) − f(x) ≥ ψγ(⟨v, y − x⟩)` for all `y ∈ K`, `x ∈ ri(K)`, `v ∈ ∂̂f(x)`;
(v) `K` is convex, the points of `ri(K)` where `∇f(x)` exists are dense in `K`, and
`f(y) − f(x) ≥ ψγ(⟨∇f(x), y − x⟩)` for all `y ∈ K` and `x ∈ ri(K)` where `∇f(x)` exists, the
gradient taken with respect to `aff(K)`.

**Formalization Note** `∂f` is the published `NonconvexSplitting.Shared.LimitingSubdiff` and
`∂̂f` the published `NAPPAL.VPEB.frechetSubdiff` (empty where `f x = +∞`);
`ri(K)` is `intrinsicInterior ℝ K`; "dense in `K`" is `K ⊆ closure S`; `∇f(x)` is any `g` with
`IsRelGrad f K x g` (such a `g` is unique). For `γ > 0` every tilt is defined, so (iv), (v) carry
no definedness clause. -/
theorem theorem_8 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (f : E → EReal)
    (hf : IsProper f) (hlsc : LowerSemicontinuous f) :
    List.TFAE
      [TiltedConvex γ f,
       TiltedConvexWrt γ f (LimitingSubdiff f),
       TiltedConvexWrt γ f (frechetSubdiff f),
       Convex ℝ (effDom f) ∧
         ∀ y ∈ effDom f, ∀ x ∈ intrinsicInterior ℝ (effDom f), ∀ v ∈ frechetSubdiff f x,
           psi γ ((⟪v, y - x⟫_ℝ : ℝ) : EReal) ≤ f y - f x,
       Convex ℝ (effDom f) ∧
         effDom f ⊆ closure {x | x ∈ intrinsicInterior ℝ (effDom f) ∧
           ∃ g : E, IsRelGrad f (effDom f) x g} ∧
         ∀ y ∈ effDom f, ∀ x ∈ intrinsicInterior ℝ (effDom f), ∀ g : E,
           IsRelGrad f (effDom f) x g → psi γ ((⟪g, y - x⟫_ℝ : ℝ) : EReal) ≤ f y - f x] := by sorry

end TiltedCvx
