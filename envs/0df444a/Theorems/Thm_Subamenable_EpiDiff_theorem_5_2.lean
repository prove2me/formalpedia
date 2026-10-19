-- Prove2me | Theorems.Thm_Subamenable_EpiDiff_theorem_5_2
-- name    : Subamenable.EpiDiff.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:14:38.648321+00:00
-- url     : https://prove2.me/theorems/21fc1255-6ed3-46e1-97d7-a9730612e6e6
-- title:
--   Theorem 5.2 — proper twice epi-differentiability and the attained maximum formula
-- statement:
--   Let $\varphi:\mathbb R^n\to(-\infty,+\infty]$ be fully subamenable at $\bar x$ through the local representation $\varphi=\vartheta\circ f$, where $\vartheta$ is convex piecewise linear-quadratic, $f$ is twice differentiable at $\bar x$, and MSQC holds. For every $\bar v\in\partial\varphi(\bar x)$, the function $\varphi$ is properly twice epi-differentiable at $\bar x$ for $\bar v$, and for every $w\in\mathbb R^n$,
--
--   $$d^2\varphi(\bar x,\bar v)(w)=\max_{\lambda\in\Lambda(\bar x,\bar v)}\left\{d^2\vartheta(f(\bar x),\lambda)(\nabla f(\bar x)w)+\langle\lambda,\nabla^2 f(\bar x)(w,w)\rangle\right\}.$$
--
--   Here $\Lambda(\bar x,\bar v)=\{\lambda\in\partial\vartheta(f(\bar x)):\nabla f(\bar x)^*\lambda=\bar v\}$. The formula expresses the composite second subderivative entirely through the outer function, derivatives of $f$, and an attained multiplier maximum.
--
--   **Formalization Note** `IsGreatest` asserts attainment, including at directions where the value is $+\infty$. Proper twice epi-differentiability uses the equivalent recovery-sequence test (2.16). The local equality and all MSQC and PWLQ assumptions are carried by the representation predicate; the limiting subdifferential uses the published analytic definition, agreeing here with the paper's geometric one.
-- source:
--   Mohammadi, Mordukhovich, Sarabi, Variational analysis of composite models with applications to continuous optimization, arXiv:1905.08837v2, p. 22, Theorem 5.2, (5.3)

import Mathlib
import Definitions.Def_Subamenable_EpiDiff_Composite

namespace Subamenable.EpiDiff

theorem theorem_5_2 {n m : ℕ} (phi : E n → EReal) (theta : E m → EReal)
    (f : E n → E m) (xbar vbar : E n)
    (h : IsFullySubamenableRep phi theta f xbar)
    (hv : vbar ∈ NonconvexSplitting.Shared.LimitingSubdiff phi xbar) :
    IsProperlyTwiceEpiDiff phi xbar vbar ∧
      ∀ w : E n,
        IsGreatest
          {e : EReal | ∃ lam ∈ Lam theta f xbar vbar,
            e = multiplierValue theta f xbar w lam}
          (secondSubderiv phi xbar vbar w) := by sorry

end Subamenable.EpiDiff
