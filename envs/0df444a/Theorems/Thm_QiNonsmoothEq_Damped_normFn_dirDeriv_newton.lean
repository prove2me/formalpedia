-- Prove2me | Theorems.Thm_QiNonsmoothEq_Damped_normFn_dirDeriv_newton
-- name    : QiNonsmoothEq.Damped.normFn_dirDeriv_newton
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:37:32.124354+00:00
-- url     : https://prove2.me/theorems/94be5cce-618e-4f3a-b69f-c5f37c5be557
-- title:
--   Proof of Theorem 4.3, p. 237 (Lemma 1 of [7]) — along a solution d of (3.12), g'(x; d) = −2g(x)
-- statement:
--   Let $F:\mathbb R^n\to\mathbb R^n$ be locally Lipschitz and let $g(x)=\tfrac12\|F(x)\|^2$ be its norm function. Let $y,d\in\mathbb R^n$ and suppose that the directional derivative $F'(y;d)$ exists and solves the generalized Newton equation $F(y)+F'(y;d)=0$. Then the one-sided directional derivative $g'(y;d)$ exists and
--   $$g'(y;d)=-2g(y).$$
--
--   Equivalently $2g(x^k)=-g'(x^k;d^k)$ for every iterate of the damped Newton method. It says that a Newton direction is a descent direction for $g$ with a rate tied to $g$ itself, which is what makes the Armijo test (4.1) accept the unit step near a regular zero.
--
--   **Formalization Note** The conclusion states both that the one-sided limit defining $g'(y;d)$ exists with value $-2g(y)$ and that the `dirDeriv` value equals $-2g(y)$, so that the default value of an undefined limit never enters later statements. The paper cites this as Lemma 1 of Pang's paper [7] and does not prove it.
-- source:
--   Qi, Convergence analysis of some algorithms for solving nonsmooth equations, Math. Oper. Res. 18 (1993), p. 237, proof of Theorem 4.3 ("By Lemma 1 of [7], 2g(x^k) = −g'(x^k; d^k)")

import Mathlib
import Definitions.Def_QiNonsmoothEq_Damped_Setting

namespace QiNonsmoothEq.Damped

open Filter Topology NonsmoothNewton.Local NonsmoothNewton.Shared

theorem normFn_dirDeriv_newton {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hF : LocallyLipschitz F)
    (y dy : EuclideanSpace ℝ (Fin n)) (hd : HasDirDerivAt F y dy (-F y)) :
    HasDirDerivAt (normFn F) y dy (-2 * normFn F y) ∧
      dirDeriv (normFn F) y dy = -2 * normFn F y := by sorry

end QiNonsmoothEq.Damped
