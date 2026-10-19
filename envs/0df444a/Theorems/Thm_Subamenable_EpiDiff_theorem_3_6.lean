-- Prove2me | Theorems.Thm_Subamenable_EpiDiff_theorem_3_6
-- name    : Subamenable.EpiDiff.theorem_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:14:44.737995+00:00
-- url     : https://prove2.me/theorems/26a6621f-825b-4244-8352-9e4b79a7d035
-- title:
--   Theorem 3.6 — limiting-subgradient chain rule under MSQC
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R^m$ be strictly differentiable at $\bar x$. Let $\vartheta:\mathbb R^m\to(-\infty,+\infty]$ be convex, lower semicontinuous around $f(\bar x)$, and Lipschitz there relative to its domain. If $f(\bar x)$ belongs to that domain and MSQC holds at $\bar x$, then $\vartheta\circ f$ is lower regular there and
--
--   $$\partial(\vartheta\circ f)(\bar x)=\widehat\partial(\vartheta\circ f)(\bar x)=\nabla f(\bar x)^*\partial\vartheta(f(\bar x)).$$
--
--   This identifies the limiting and regular subgradients and explains the multiplier representation used in the second-order formula.
--
--   **Formalization Note** Domain membership is implicit in the source; exclusion of $-\infty$ expresses its codomain. The regular and limiting subgradients use the published analytic definitions, which agree with the paper's geometric definitions at these lower semicontinuous functions.
-- source:
--   Mohammadi, Mordukhovich, Sarabi, Variational analysis of composite models with applications to continuous optimization, arXiv:1905.08837v2, p. 13, Theorem 3.6, (3.11)

import Mathlib
import Definitions.Def_Subamenable_EpiDiff_Composite

open Filter Topology

namespace Subamenable.EpiDiff

theorem theorem_3_6 {n m : ℕ} (theta : E m → EReal) (f : E n → E m)
    (xbar : E n) (htheta : ∀ y, theta y ≠ ⊥) (hdom : f xbar ∈ dom theta)
    (hstrict : HasStrictFDerivAt f (fderiv ℝ f xbar) xbar)
    (hconv : Convex ℝ {p : E m × ℝ | theta p.1 ≤ (p.2 : EReal)})
    (hlsc : ∀ᶠ y in 𝓝 (f xbar), LowerSemicontinuousAt theta y)
    (ell kappa : ℝ) (hlip : LipschitzRelativeAt theta (f xbar) ell)
    (hmsqc : MSQC theta f xbar kappa) :
    NonconvexSplitting.Shared.LimitingSubdiff (fun x => theta (f x)) xbar =
      {v | NonconvexSplitting.Shared.IsRegularSubgrad (fun x => theta (f x)) xbar v} ∧
    {v | NonconvexSplitting.Shared.IsRegularSubgrad (fun x => theta (f x)) xbar v} =
      (fderiv ℝ f xbar).adjoint ''
        NonconvexSplitting.Shared.LimitingSubdiff theta (f xbar) := by sorry

end Subamenable.EpiDiff
