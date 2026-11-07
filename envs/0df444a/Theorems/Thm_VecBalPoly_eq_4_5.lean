-- Prove2me | Theorems.Thm_VecBalPoly_eq_4_5
-- name    : VecBalPoly.eq_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T23:12:55.951047+00:00
-- url     : https://prove2.me/theorems/498b8f73-3487-45c3-99dd-92b6da725497
-- title:
--   Displays (4.4)–(4.5) — barrier derivatives and their bounds
-- statement:
--   At a state after cleanup, for a medium row $i$ and a sign $\sigma$, the barrier $u_{i\sigma}$ (2.4), as a function of the coloring with $V,T_i,c_i,r_i$ fixed, has gradient and Hessian in the active coordinates
--   $$g_{i\sigma}:=\nabla u_{i\sigma}=\frac{\sigma b_i}{r_i}-\frac{p_i\circ x_V}{r_i^2},\qquad\nabla^2u_{i\sigma}=-\frac1{r_i^2}\operatorname{diag}(p_i),$$
--   and
--   $$\|g_{i\sigma}\|_2\le2,\qquad(g_{i\sigma})_j^2\le\frac{2(p_i)_j}{r_i^2},\qquad\|\nabla^2u_{i\sigma}\|_{\mathrm{op}}\le\frac1K.$$
--
--   These bounds control how fast a barrier can move along an update and feed the curvature comparison of Proposition 4.5 and the Taylor bound of Lemma C.1.
--
--   Differences from the source:
--   - generalization: a state after cleanup of Algorithm 2.2 → any state satisfying IsClean (cube, V = {|x_j| < 1}, T_i ⊆ V, (2.2), (2.3) on medium rows, column norms ≤ 1); reason: every post-cleanup state of a run satisfies these conditions, and the proof uses only them
--   - encoding: ∇u_{iσ} and ∇²u_{iσ} in the active coordinates → fderiv of y ↦ u_{iσ}(y) along h supported on V equals ⟨g_{iσ}, h⟩; its second fderiv along h, h' equals −(1/r_i²) Σ_j (p_i)_j h_j h'_j; reason: the gradient and Hessian are the representing vector and matrix of these derivatives
--   - encoding: ‖∇²u_{iσ}‖_op ≤ 1/K → (p_i)_j / r_i² ≤ 1/K for every j; reason: ∇²u_{iσ} = −diag(p_i)/r_i² (the second clause), and the operator norm of a diagonal matrix with nonnegative entries is its largest entry
--   - generalization: m ≥ 1 (the standing assumption of Theorem 1.1) → m = 0 also allowed; reason: with no rows there are no row constraints and the row sums are empty; the source's cases m ≥ 1 are included unchanged
--   - encoding: row, column and sign indices i ∈ [m], j ∈ [n], σ ∈ {−1, 1} → Fin m, Fin n (0-based) and σ : Bool with sgn true = 1, sgn false = −1; reason: Lean conventions; same instances
-- source:
--   S. Guo, E. X. Fang, J. Lu, Vector Balancing in Polynomial Time, arXiv:2609.23540 (held file sha256 b777ade4…), (4.4), p.10 and (4.5), p.11 (PDF pp.11–12)

import Mathlib
import Definitions.Def_VecBalPoly_IsClean
import Definitions.Def_VecBalPoly_u

namespace VecBalPoly

open Matrix

/-- **Displays (4.4) and (4.5) (barrier derivatives and their bounds).**
Guo, Fang, Lu, *Vector Balancing in Polynomial Time*, arXiv:2609.23540 (held file sha256
b777ade4…), §4.3, (4.4), p.10 and (4.5), p.11 (PDF pp.11–12): "For a medium row, differentiating (2.4)
yields giσ := ∇uiσ = σbi/ri − (pi ◦ xV)/r²i, ∇²uiσ = −(1/r²i) diag(pi), (4.4) where ◦ denotes
coordinatewise multiplication. The spreading and scale conditions also give ∥giσ∥2 ≤ 2,
(giσ)²j ≤ 2(pi)j/r²i, ∥∇²uiσ∥op ≤ 1/K. (4.5)"

**Formalization Note** At a state after cleanup (`IsClean`) and a medium row: the derivative of
`y ↦ u_{iσ}(y)` (`V, Tᵢ, cᵢ, rᵢ` fixed) along every `h` supported on `V` is `⟨g_{iσ}, h⟩`,
and its second derivative along `h, h'` is `−(1/rᵢ²)∑ⱼ (pᵢ)ⱼhⱼh'ⱼ`; then the three bounds.
The operator norm of the diagonal matrix `−(1/rᵢ²)diag(pᵢ)` is `maxⱼ (pᵢ)ⱼ/rᵢ²`, so its bound is
written coordinatewise. -/
theorem eq_4_5 :
    ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (st : St m n), IsClean A st →
      ∀ i σ, IsMedium A st i →
        (∀ h : Fin n → ℝ, (∀ j, j ∉ st.V → h j = 0) →
          fderiv ℝ (fun y => u A { st with x := y } i σ) st.x h = gradU A st i σ ⬝ᵥ h) ∧
        (∀ h h' : Fin n → ℝ, (∀ j, j ∉ st.V → h j = 0) → (∀ j, j ∉ st.V → h' j = 0) →
          fderiv ℝ (fun y => fderiv ℝ (fun y' => u A { st with x := y' } i σ) y h) st.x h' =
            -(1 / st.r i ^ 2) * ∑ j, p A st i j * h j * h' j) ∧
        Real.sqrt (∑ j, gradU A st i σ j ^ 2) ≤ 2 ∧
        (∀ j, gradU A st i σ j ^ 2 ≤ 2 * p A st i j / st.r i ^ 2) ∧
        (∀ j, p A st i j / st.r i ^ 2 ≤ 1 / K) := by sorry

end VecBalPoly
