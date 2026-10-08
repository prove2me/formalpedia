-- Prove2me | Theorems.Thm_RetailVariety_Fashion_g_convex
-- name    : RetailVariety.Fashion.g_convex
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:59:17.266979+00:00
-- url     : https://prove2.me/theorems/31fc5cda-8221-4fd2-8b3f-9bb19402a276
-- title:
--   Proof of Theorem 3 — $g$ and $g^T$ are convex on $[0,\infty)$ and vanish at $0$
-- statement:
--   Let $0<c<p$, $\lambda>0$, $\sigma>0$, $0\le\beta<1$ and $L>0$, and let $g$, $g^T$ be the functions of the proof of Theorem 3:
--   $$g(x)=\frac{(p-c)\lambda}{L}\,x-\frac{p\sigma\lambda^{\beta}e^{-z^2/2}}{\sqrt{2\pi}\,L^{\beta}}\,x^{\beta},\qquad g^{T}(x)=\frac{\lambda}{L}(px-cL)^{+}.$$
--   Then $g$ and $g^T$ are convex on $[0,\infty)$, $g^T(0)=0$, and $g(0)=0$ when $\beta>0$.
--
--   Convexity is what allows Lemma 2 to be applied; $g(0)=0$ is what makes the padded zeros of $w'$ contribute nothing.
--
--   **Formalization Note.** The paper writes $0<\beta<1$ here. Convexity also holds at $\beta=0$; only $g(0)=0$ needs $\beta>0$ (with real powers $0^0=1$).
-- source:
--   van Ryzin & Mahajan, On the Relationship Between Inventory Costs and Variety Benefits in Retail Assortments, Management Science 45(11), 1999, p. 1506, proof of Theorem 3

import Mathlib
import Definitions.Def_RetailVariety_Fashion_ProofObjects

namespace RetailVariety.Fashion

/-- p. 1506: for `L > 0`, `g` and `g^T` are convex on `[0, ∞)`, `g^T(0) = 0`, and `g(0) = 0` when
`0 < β`. -/
theorem g_convex (p c lam σ β L : ℝ) (hc : 0 < c) (hcp : c < p) (hlam : 0 < lam)
    (hσ : 0 < σ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hL : 0 < L) :
    ConvexOn ℝ (Set.Ici 0) (gFun p c lam σ β L) ∧
      ConvexOn ℝ (Set.Ici 0) (gFunT p c lam L) ∧
      gFunT p c lam L 0 = 0 ∧
      (0 < β → gFun p c lam σ β L 0 = 0) := by sorry

end RetailVariety.Fashion
