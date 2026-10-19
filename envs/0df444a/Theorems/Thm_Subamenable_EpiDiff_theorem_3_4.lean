-- Prove2me | Theorems.Thm_Subamenable_EpiDiff_theorem_3_4
-- name    : Subamenable.EpiDiff.theorem_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:14:35.869983+00:00
-- url     : https://prove2.me/theorems/c96e12e5-a600-4e28-9664-0a783fe5ed4b
-- title:
--   Theorem 3.4 — subderivative chain rule under MSQC
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R^m$ be differentiable at $\bar x$, and let $\vartheta:\mathbb R^m\to(-\infty,+\infty]$ be Lipschitz near $f(\bar x)$ relative to its domain. Suppose $f(\bar x)$ is in that domain and the metric subregularity qualification condition holds at $\bar x$ with a nonnegative modulus. Then, for every $w\in\mathbb R^n$,
--
--   $$d(\vartheta\circ f)(\bar x)(w)=d\vartheta(f(\bar x))(\nabla f(\bar x)w).$$
--
--   This equality replaces the usual one-sided chain estimate and supplies the first-order identity used in the main second-order theorem.
--
--   **Formalization Note** The domain membership is implicit in the source's use of $d\vartheta(f(\bar x))$. The paper prints $w\in\mathbb R^m$ after (3.9); the direction is in $\mathbb R^n$. The explicit exclusion of $-\infty$ expresses the paper's codomain.
-- source:
--   Mohammadi, Mordukhovich, Sarabi, Variational analysis of composite models with applications to continuous optimization, arXiv:1905.08837v2, p. 11, Theorem 3.4, (3.9)

import Mathlib
import Definitions.Def_Subamenable_EpiDiff_Composite

namespace Subamenable.EpiDiff

theorem theorem_3_4 {n m : ℕ} (theta : E m → EReal) (f : E n → E m)
    (xbar : E n) (htheta : ∀ y, theta y ≠ ⊥) (hdom : f xbar ∈ dom theta)
    (hdf : DifferentiableAt ℝ f xbar)
    (ell kappa : ℝ) (hlip : LipschitzRelativeAt theta (f xbar) ell)
    (hmsqc : MSQC theta f xbar kappa) :
    ∀ w : E n,
      subderiv (fun x => theta (f x)) xbar w =
        subderiv theta (f xbar) (fderiv ℝ f xbar w) := by sorry

end Subamenable.EpiDiff
