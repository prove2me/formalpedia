-- Prove2me | Theorems.Thm_Subamenable_EpiDiff_corollary_4_7
-- name    : Subamenable.EpiDiff.corollary_4_7
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-21T23:47:53.432563+00:00
-- url     : https://prove2.me/theorems/e1d29be1-7f73-4206-8c43-3c70793d1541
-- title:
--   Corollary 4.7 — primal–dual relationships along critical directions
-- statement:
--   Let $\varphi$ be fully subamenable at $\bar x$ through the local representation $\varphi=\vartheta\circ f$ ($\vartheta$ convex piecewise linear-quadratic, $f$ twice differentiable at $\bar x$, MSQC at $\bar x$), let $\bar v\in\partial\varphi(\bar x)$, and let $w$ be a critical direction, $w\in K_\varphi(\bar x,\bar v)=\{w: d\varphi(\bar x)(w)=\langle\bar v,w\rangle\}$. Consider the primal piecewise linear-quadratic program
--
--   $$\min_{z\in\mathbb R^n}\; P(z):=d^2\vartheta(f(\bar x))\big(\nabla f(\bar x)w;\ \nabla f(\bar x)z+\nabla^2 f(\bar x)(w,w)\big)-\langle\bar v,z\rangle$$
--
--   (problem (4.14), built from the parabolic subderivative of $\vartheta$) and the dual program
--
--   $$\max_{\lambda\in\Lambda(\bar x,\bar v)}\; d^2\vartheta(f(\bar x),\lambda)(\nabla f(\bar x)w)+\langle\lambda,\nabla^2 f(\bar x)(w,w)\rangle ,$$
--
--   where $\Lambda(\bar x,\bar v)=\{\lambda\in\partial\vartheta(f(\bar x)):\nabla f(\bar x)^*\lambda=\bar v\}$. Then the primal problem admits an optimal solution $\bar z$, the dual maximum is attained, and the two optimal values coincide:
--
--   $$P(\bar z)=\min_z P(z)=\max_{\lambda\in\Lambda(\bar x,\bar v)}\Big\{d^2\vartheta(f(\bar x),\lambda)(\nabla f(\bar x)w)+\langle\lambda,\nabla^2 f(\bar x)(w,w)\rangle\Big\}.$$
--
--   **Formalization Note.** The paper states the duality for problem (4.9) (maximization over $\lambda\in\Lambda(\bar x,\bar v)$ with $d\vartheta(f(\bar x))(\nabla f(\bar x)w)=\langle\nabla f(\bar x)w,\lambda\rangle$); by Theorem 4.5(ii) its feasible and optimal sets coincide with those of (4.7), the maximization over $\Lambda(\bar x,\bar v)$ used here. The dual statement is expressed with `IsGreatest`, which asserts both attainment and the value. Values live in $[-\infty,\infty]$; the parabolic subderivative is the published `parabolicSubderiv`.
-- source:
--   Mohammadi, Mordukhovich, Sarabi, Variational analysis of composite models with applications to continuous optimization, arXiv:1905.08837v2, p. 20, Corollary 4.7 (i)-(ii), problems (4.9) [=(4.7) by Theorem 4.5(ii)] and (4.14)

import Mathlib
import Definitions.Def_Subamenable_EpiDiff_Composite

open scoped InnerProductSpace

namespace Subamenable.EpiDiff

theorem corollary_4_7 {n m : ℕ} (phi : E n → EReal) (theta : E m → EReal)
    (f : E n → E m) (xbar vbar : E n)
    (h : IsFullySubamenableRep phi theta f xbar)
    (hv : vbar ∈ NonconvexSplitting.Shared.LimitingSubdiff phi xbar)
    (w : E n) (hw : w ∈ criticalCone phi xbar vbar) :
    ∃ zbar : E n,
      (∀ z : E n,
        parabolicSubderiv theta (f xbar) (fderiv ℝ f xbar w)
            (fderiv ℝ f xbar zbar + fderiv ℝ (fderiv ℝ f) xbar w w) -
            ((⟪vbar, zbar⟫_ℝ : ℝ) : EReal) ≤
          parabolicSubderiv theta (f xbar) (fderiv ℝ f xbar w)
            (fderiv ℝ f xbar z + fderiv ℝ (fderiv ℝ f) xbar w w) -
            ((⟪vbar, z⟫_ℝ : ℝ) : EReal)) ∧
      IsGreatest
        {e : EReal | ∃ lam ∈ Lam theta f xbar vbar,
          e = multiplierValue theta f xbar w lam}
        (parabolicSubderiv theta (f xbar) (fderiv ℝ f xbar w)
            (fderiv ℝ f xbar zbar + fderiv ℝ (fderiv ℝ f) xbar w w) -
          ((⟪vbar, zbar⟫_ℝ : ℝ) : EReal)) := by sorry

end Subamenable.EpiDiff
