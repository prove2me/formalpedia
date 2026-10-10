-- Prove2me | Theorems.Thm_StrictCQ_SAKKT_proposition_4_4
-- name    : StrictCQ.SAKKT.proposition_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T23:32:04.245991+00:00
-- url     : https://prove2.me/theorems/0a0eaee0-9259-426f-83e9-44c34c83b7fa
-- title:
--   Proposition 4.4, p. 11 — normal vectors of Ω(x, 0) at x + ε are active-gradient combinations, and N_{Ω(x,0)}(x + ε) ⊂ N_{Ω(x,0)}(x)
-- statement:
--   Let the constraint functions be continuously differentiable, let $x,\varepsilon\in\mathbb R^n$, and suppose $x+\varepsilon\in\Omega(x,0)$, where
--   $$\Omega(x,0)=\{z:\ \langle\nabla h_i(x),z-x\rangle=0\ \forall i,\ \ \langle\nabla g_j(x),z-x\rangle\le0 \text{ if } g_j(x)\ge0\}.$$
--   Then:
--
--   1. every $w\in N_{\Omega(x,0)}(x+\varepsilon)$ can be written as
--   $$w=\sum_{i=1}^m\lambda_i\nabla h_i(x)+\sum_{j:\,g_j(x)\ge0}\mu_j\nabla g_j(x),$$
--   with $\lambda_i\in\mathbb R$, $\mu_j\ge0$, and $\mu_j\langle\nabla g_j(x),\varepsilon\rangle=0$ whenever $g_j(x)\ge0$;
--   2. $N_{\Omega(x,0)}(x+\varepsilon)\subseteq N_{\Omega(x,0)}(x)$.
--
--   The second part lets one move normal vectors from the projected point back to the base point $x$; this is how the AGP(0) sequences in the proof of Theorem 4.5 produce elements of $N_{\Omega(x^k,0)}(x^k)$.
--
--   **Formalization Note** The page writes "$x$ and $\varepsilon$ be elements in $\mathbb R^m$"; they are points of $\mathbb R^n$, where $\Omega(x,0)$ lives. The sum over $\{j: g_j(x)\ge 0\}$ is written as a sum over all $j$ with $\mu_j=0$ whenever $g_j(x)<0$. The $\mathrm C^1$ hypothesis is the paper's standing assumption; only the gradient vectors at $x$ enter the statement.
-- source:
--   Andreani, Martínez, Ramos & Silva, Strict constraint qualifications and sequential optimality conditions for constrained optimization, Optimization Online 5197 (version of November 12, 2015), p. 11, Proposition 4.4

import Mathlib
import Definitions.Def_StrictCQ_SAKKT_Setting

open Filter Topology InnerProductSpace

namespace StrictCQ.SAKKT

/-- Proposition 4.4: if `x + ε ∈ Ω(x, 0)`, every element of `N_{Ω(x,0)}(x + ε)` is
`Σ λᵢ ∇hᵢ(x) + Σ_{gⱼ(x) ≥ 0} μⱼ ∇gⱼ(x)` with `μⱼ ≥ 0` and `μⱼ ⟨∇gⱼ(x), ε⟩ = 0` when `gⱼ(x) ≥ 0`
(here `μⱼ = 0` when `gⱼ(x) < 0`, so the sum runs over all `j`); and
`N_{Ω(x,0)}(x + ε) ⊆ N_{Ω(x,0)}(x)`. -/
theorem proposition_4_4 {n m p : ℕ} (C : Constraints n m p) (hC : C.IsC1)
    (x ε : EuclideanSpace ℝ (Fin n)) (hxε : x + ε ∈ C.linSet x 0) :
    (∀ w ∈ StrictCQ.AGP.normalCone (C.linSet x 0) (x + ε),
      ∃ (lam : Fin m → ℝ) (mu : Fin p → ℝ), (∀ j, 0 ≤ mu j) ∧ (∀ j, C.g j x < 0 → mu j = 0) ∧
        (∀ j, 0 ≤ C.g j x → mu j * ⟪gradient (C.g j) x, ε⟫_ℝ = 0) ∧
        w = ∑ i, lam i • gradient (C.h i) x + ∑ j, mu j • gradient (C.g j) x) ∧
    StrictCQ.AGP.normalCone (C.linSet x 0) (x + ε) ⊆ StrictCQ.AGP.normalCone (C.linSet x 0) x := by sorry

end StrictCQ.SAKKT
