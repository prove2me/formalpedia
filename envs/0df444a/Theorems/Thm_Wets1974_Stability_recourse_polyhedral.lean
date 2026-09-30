-- Prove2me | Theorems.Thm_Wets1974_Stability_recourse_polyhedral
-- name    : Wets1974.Stability.recourse_polyhedral
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T14:35:21.590513+00:00
-- url     : https://prove2.me/theorems/ea8bff75-77d3-4b41-89fd-7f63343405de
-- title:
--   Proposition 7.5 — $Q(x,\xi)$ is convex polyhedral in $x$ on $K_2$, concave polyhedral in $q$, convex polyhedral in $(p,T)$
-- statement:
--   Consider the recourse function $Q(x,\xi)=\min\{q(\xi)y\mid Wy=p(\xi)-T(\xi)x,\ y\ge0\}$ of a stochastic program with fixed recourse $W$, the support $\tilde\Xi$ of the law $\mu$ of $\xi$, and the induced constraint set $K_2$ (Corollary 4.5). Then:
--
--   1. **In $x$.** For each $\xi\in\tilde\Xi$, either $x\mapsto Q(x,\xi)$ is a finite convex polyhedral function on $K_2$ (a maximum of finitely many affine functions of $x$ there), or $Q(x,\xi)=-\infty$ for every $x\in K_2$.
--   2. **In $q$.** Fix $x$, $p$ and $T$ with $p-Tx\in\operatorname{pos}W$. Then $q\mapsto Q$ is a finite concave polyhedral function (a minimum of finitely many affine functions of $q$) on
--   $$\operatorname{pos}(W^T,-W^T,I)=\{q \mid q\ge \pi W \text{ for some } \pi\in\mathbb R^{\bar m}\},$$
--   the set of cost vectors for which the dual of the recourse problem is feasible (Corollary 7.4).
--   3. **In $(p,T)$.** Fix $q$ and $x$. On the set $\{(p,T) \mid p-Tx\in\operatorname{pos}W\}$, either $(p,T)\mapsto Q$ is a finite convex polyhedral function (a maximum of finitely many affine functions of $(p,T)$), or it is identically $-\infty$.
--
--   Part 1 is what Theorem 7.6 uses to obtain the convexity of the expected recourse $\mathcal Q$ and its finite-or-$-\infty$ dichotomy; parts 2 and 3 describe the dependence on the random data.
--
--   **Formalization Note** In parts 2 and 3, $Q$ is the platform's `KallMayer.Recourse.PointwiseRecourse W T p q x` evaluated at arbitrary data $(q,p,T)$. Parts 1 and 3 are stated as the dichotomy of Corollary 7.3, which is what "polyhedral" means for a function that may take the value $-\infty$; part 2 is stated as Corollary 7.4, the corollary the paper's proof invokes for it (the primal problem is feasible by hypothesis, so the $+\infty$ branch of Corollary 7.4 does not occur). The paper remarks (p. 329) that the proposition extends to all $x\in\mathbb R^n$ under the $\pm\infty$ conventions; the printed statement, on $K_2$ and for $\xi\in\tilde\Xi$, is what is formalized.
-- source:
--   Wets, Stochastic Programs with Fixed Recourse: The Equivalent Deterministic Program, SIAM Review 16(3), 1974, p. 329, Proposition 7.5

import Mathlib
import Definitions.Def_Wets1974_Stability_Model

namespace Wets1974.Stability

open MeasureTheory Matrix

/-- Proposition 7.5, p. 329: `Q(x, ξ)` is a convex polyhedral function of `x` on `K₂` for each
`ξ ∈ Ξ̃`; it is concave polyhedral in `q(ξ)` and convex polyhedral in `(p(ξ), T(ξ))`.
Parts (a) and (c) are stated as the dichotomy of Corollary 7.3 (finite polyhedral, or `−∞`
throughout); part (b) as Corollary 7.4 (finite concave polyhedral on `pos (Wᵀ, −Wᵀ, I)`, the
primal problem being feasible). -/
theorem recourse_polyhedral {n nb mb : ℕ} (μ : Measure (DataSpace n nb mb))
    (W : Matrix (Fin mb) (Fin nb) ℝ) :
    -- (a) in `x` on `K₂`, for each `ξ` in the support `Ξ̃` of `μ`
    (∀ ξ ∈ μ.support,
      IsFiniteConvexPolyhedralOn (fun x => Q W x ξ) (K2 μ W) ∨
        ∀ x ∈ K2 μ W, Q W x ξ = ⊥) ∧
    -- (b) in `q`, for fixed `x` and `(p, T)` with `p − T x ∈ pos W`: finite concave polyhedral
    -- on `pos (Wᵀ, −Wᵀ, I) = {q | ∃ π, π W ≤ q}` (Corollary 7.4)
    (∀ (x : Fin n → ℝ) (p : Fin mb → ℝ) (T : Matrix (Fin mb) (Fin n) ℝ),
      p - T *ᵥ x ∈ posW W →
      IsFiniteConcavePolyhedralOn
        (fun q : Fin nb → ℝ => KallMayer.Recourse.PointwiseRecourse W T p q x)
        {q | ∃ π : Fin mb → ℝ, ∀ j, (W.transpose *ᵥ π) j ≤ q j}) ∧
    -- (c) in `(p, T)`, for fixed `q` and `x`, on `{(p, T) | p − T x ∈ pos W}`
    (∀ (x : Fin n → ℝ) (q : Fin nb → ℝ),
      IsFiniteConvexPolyhedralOn
          (fun ζ : PTSpace n mb =>
            KallMayer.Recourse.PointwiseRecourse W (Matrix.of ζ.2) ζ.1 q x)
          {ζ | ζ.1 - Matrix.of ζ.2 *ᵥ x ∈ posW W} ∨
        ∀ ζ : PTSpace n mb, ζ.1 - Matrix.of ζ.2 *ᵥ x ∈ posW W →
          KallMayer.Recourse.PointwiseRecourse W (Matrix.of ζ.2) ζ.1 q x = ⊥) := by sorry

end Wets1974.Stability
