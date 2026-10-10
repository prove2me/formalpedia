-- Prove2me | Theorems.Thm_StrictCQ_SAKKT_eq_4_23_4_24_outer_limit
-- name    : StrictCQ.SAKKT.eq_4_23_4_24_outer_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T23:33:30.570415+00:00
-- url     : https://prove2.me/theorems/1e9d679b-70ab-49ac-a8c6-a3da05f95341
-- title:
--   (4.23)–(4.24), proof of Theorem 4.5, p. 12 — AGP(0) sequences yield normal vectors ωᵏ ∈ N_{Ω(xᵏ,0)}(xᵏ) converging to −∇f(x*)
-- statement:
--   Let the constraint functions and the objective $f$ be continuously differentiable. Let $x^k\to x^*$, and let $y^k$ be the Euclidean projection of $x^k-\nabla f(x^k)$ onto $\Omega(x^k,0)$, with $y^k-x^k\to0$. Then
--   $$-\nabla f(x^*)\in\limsup_{x\to x^*}N_{\Omega(x,0)}(x).$$
--   The witnesses are $\omega^k=x^k-\nabla f(x^k)-y^k$, which belong to $N_{\Omega(x^k,0)}(y^k)\subseteq N_{\Omega(x^k,0)}(x^k)$ (4.23) and converge to $-\nabla f(x^*)$ (4.24).
--
--   This is the forward half of Theorem 4.5 before the outer semicontinuity is applied: every AGP(0) sequence for $f$ places $-\nabla f(x^*)$ in the outer limit.
--
--   **Formalization Note** The projection is a predicate ($y^k$ is a nearest point of $\Omega(x^k,0)$ to $x^k-\nabla f(x^k)$), which determines $y^k$ uniquely. The outer limit is sequential (1.6). Continuity of $\nabla f$ is where the $\mathrm C^1$ hypothesis on $f$ enters.
-- source:
--   Andreani, Martínez, Ramos & Silva, Strict constraint qualifications and sequential optimality conditions for constrained optimization, Optimization Online 5197 (version of November 12, 2015), p. 12, (4.23)–(4.24), proof of Theorem 4.5

import Mathlib
import Definitions.Def_StrictCQ_SAKKT_Setting

open Filter Topology InnerProductSpace

namespace StrictCQ.SAKKT

/-- (4.23)–(4.24): if `xᵏ → xs`, `yᵏ = P_{Ω(xᵏ,0)}(xᵏ - ∇f(xᵏ))` and `yᵏ - xᵏ → 0`, then
`ωᵏ = xᵏ - ∇f(xᵏ) - yᵏ ∈ N_{Ω(xᵏ,0)}(xᵏ)` converges to `-∇f(xs)`, so `-∇f(xs)` lies in the outer
limit of `x ↦ N_{Ω(x,0)}(x)` at `xs`. -/
theorem eq_4_23_4_24_outer_limit {n m p : ℕ} (C : Constraints n m p) (hC : C.IsC1)
    (xs : EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (x y : ℕ → EuclideanSpace ℝ (Fin n)) (hx : Tendsto x atTop (𝓝 xs))
    (hy : ∀ k, StrictCQ.AGP.IsProj (C.linSet (x k) 0) (x k - gradient f (x k)) (y k))
    (hyx : Tendsto (fun k => y k - x k) atTop (𝓝 0)) :
    -gradient f xs ∈
      StrictCQ.AGP.outerLimitWithin (fun x => StrictCQ.AGP.normalCone (C.linSet x 0) x) Set.univ xs := by sorry

end StrictCQ.SAKKT
