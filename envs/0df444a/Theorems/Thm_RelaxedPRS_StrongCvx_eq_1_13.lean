-- Prove2me | Theorems.Thm_RelaxedPRS_StrongCvx_eq_1_13
-- name    : RelaxedPRS.StrongCvx.eq_1_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:11:45.827394+00:00
-- url     : https://prove2.me/theorems/dace991d-0c3b-49df-83bf-a3ecbcfebe28
-- title:
--   (1.13) — strong convexity and gradient regularity lower bound
-- statement:
--   Let $f:H\to(-\infty,+\infty]$ be closed, proper, convex, and $\mu$-strongly convex, where $\mu\ge0$. Let $\beta\ge0$; if $\beta>0$, assume that $f$ is real-valued, differentiable, and has a $\beta^{-1}$-Lipschitz gradient. At points $x,y$ with subgradients $u\in\partial f(x)$ and $v\in\partial f(y)$,
--   $$f(x)\ge f(y)+\langle x-y,v\rangle+\max\left\{\frac\mu2\|x-y\|^2,\frac\beta2\|u-v\|^2\right\}.$$
--   This is the paper's regularity inequality, used in both fundamental PRS bounds.
-- source:
--   Davis & Yin, Faster convergence rates of relaxed Peaceman-Rachford and ADMM under regularity assumptions, arXiv:1407.5210v3, p. 7, §1.10, (1.13); p. 8, (1.14)

import Mathlib
import Definitions.Def_RelaxedPRS_StrongCvx_Setting

open scoped InnerProductSpace

namespace RelaxedPRS.StrongCvx

/-- Inequality (1.13), p. 7, at points admitting the specified subgradients. -/
theorem eq_1_13 {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → EReal) (hf : ThreeOpSplitting.ConvexRates.IsProperClosedConvex f)
    (μ β : ℝ) (hμ : 0 ≤ μ) (hβ : 0 ≤ β)
    (hsc : IsStrongCvxE μ f) (hl : 0 < β → HasLipGrad β f)
    (x y u v : H)
    (hu : u ∈ MoreauProx.Characterization.subgrad f x)
    (hv : v ∈ MoreauProx.Characterization.subgrad f y) :
    f y + ((⟪x - y, v⟫_ℝ + auxS μ β x y u v : ℝ) : EReal) ≤ f x := by sorry

end RelaxedPRS.StrongCvx
