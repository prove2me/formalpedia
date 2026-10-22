-- Prove2me | Theorems.Thm_Subamenable_EpiDiff_eq_4_10
-- name    : Subamenable.EpiDiff.eq_4_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:14:47.994406+00:00
-- url     : https://prove2.me/theorems/8b08e3ca-244f-481e-8e79-cfa6b0270d59
-- title:
--   Equation (4.10) — lower bound in the second-order chain rule
-- statement:
--   Suppose $\varphi$ is fully subamenable at $\bar x$ through $\vartheta\circ f$, and let $\bar v\in\partial\varphi(\bar x)$. Every multiplier $\lambda\in\Lambda(\bar x,\bar v)$ and every direction $w\in\mathbb R^n$ satisfy
--
--   $$d^2\varphi(\bar x,\bar v)(w)\ge d^2\vartheta(f(\bar x),\lambda)(\nabla f(\bar x)w)+\langle\lambda,\nabla^2 f(\bar x)(w,w)\rangle.$$
--
--   This is the lower-bound half of the main formula (5.3), stated in the proof of Theorem 4.5.
-- source:
--   Mohammadi, Mordukhovich, Sarabi, Variational analysis of composite models with applications to continuous optimization, arXiv:1905.08837v2, p. 19, (4.10), proof of Theorem 4.5

import Mathlib
import Definitions.Def_Subamenable_EpiDiff_Composite

namespace Subamenable.EpiDiff

theorem eq_4_10 {n m : ℕ} (phi : E n → EReal) (theta : E m → EReal)
    (f : E n → E m) (xbar vbar : E n)
    (h : IsFullySubamenableRep phi theta f xbar)
    (hv : vbar ∈ NonconvexSplitting.Shared.LimitingSubdiff phi xbar) :
    ∀ w : E n, ∀ lam ∈ Lam theta f xbar vbar,
      multiplierValue theta f xbar w lam ≤ secondSubderiv phi xbar vbar w := by sorry

end Subamenable.EpiDiff
