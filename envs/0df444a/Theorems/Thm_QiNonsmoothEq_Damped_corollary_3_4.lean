-- Prove2me | Theorems.Thm_QiNonsmoothEq_Damped_corollary_3_4
-- name    : QiNonsmoothEq.Damped.corollary_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:37:31.303524+00:00
-- url     : https://prove2.me/theorems/f63dc7c1-7869-4de1-8d0a-9cf36224cd65
-- title:
--   Corollary 3.4, p. 236 — near a semismooth, strongly BD-regular zero, a solution d of F(x) + F'(x; d) = 0 contracts the error and the residual by any factor ε
-- statement:
--   Let $F:\mathbb R^n\to\mathbb R^n$ be locally Lipschitz and let $x^*$ be a zero of $F$. Assume that $F$ is semismooth and strongly BD-regular at $x^*$ (every $V\in\partial_B F(x^*)$ is nonsingular), and that $F$ is semismooth at every point of some neighbourhood of $x^*$.
--
--   Then for every $\varepsilon>0$ there is $\delta>0$ such that for every $x$ with $\|x-x^*\|\le\delta$ and every $d$ solving the generalized Newton equation
--   $$F(x)+F'(x;d)=0,$$
--   we have
--   $$\|x+d-x^*\|\le\varepsilon\|x-x^*\|\qquad\text{and}\qquad\|F(x+d)\|\le\varepsilon\|F(x)\|.$$
--
--   This is the local engine of the damped Newton analysis: near such a zero, a full step along any solution of (3.12) is superlinearly contracting both in the error and in the residual.
--
--   **Formalization Note** The paper prints "for any $\varepsilon\ge 0$"; at $\varepsilon=0$ the claim would force $x+d=x^*$ exactly, which is false in general, so the statement is posed for $\varepsilon>0$. Semismoothness on a neighbourhood of $x^*$ is an added hypothesis: the paper's proof uses (2.16), $F'(x;d)=Vd$ for some $V\in\partial_B F(x)$, which Lemma 2.6 establishes only at points $x$ where $F$ is semismooth, while the printed hypotheses give semismoothness at $x^*$ alone. "(3.12) is solvable for $d$" is encoded as: the directional derivative of $F$ at $x$ along $d$ exists and equals $-F(x)$.
-- source:
--   Qi, Convergence analysis of some algorithms for solving nonsmooth equations, Math. Oper. Res. 18 (1993), p. 236, Corollary 3.4

import Mathlib
import Definitions.Def_QiNonsmoothEq_Damped_Setting

namespace QiNonsmoothEq.Damped

open Filter Topology NonsmoothNewton.Local NonsmoothNewton.Shared

theorem corollary_3_4 {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hF : LocallyLipschitz F) (xstar : EuclideanSpace ℝ (Fin n)) (hzero : F xstar = 0)
    (hss : SemismoothAt F xstar) (hreg : StronglyBDRegularAt F xstar)
    (hssN : ∀ᶠ y in 𝓝 xstar, SemismoothAt F y) :
    ∀ ε > 0, ∃ δ > 0, ∀ y : EuclideanSpace ℝ (Fin n), ‖y - xstar‖ ≤ δ →
      ∀ dy : EuclideanSpace ℝ (Fin n), HasDirDerivAt F y dy (-F y) →
        ‖y + dy - xstar‖ ≤ ε * ‖y - xstar‖ ∧ ‖F (y + dy)‖ ≤ ε * ‖F y‖ := by sorry

end QiNonsmoothEq.Damped
