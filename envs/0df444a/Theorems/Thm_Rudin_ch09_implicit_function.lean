-- Prove2me | Theorems.Thm_Rudin_ch09_implicit_function
-- name    : Rudin.ch09_implicit_function
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T02:21:23.700426+00:00
-- url     : https://prove2.me/theorems/12053ca5-e868-4ee0-b661-593cc9de8fca
-- title:
--   Theorem 9.28 — implicit function theorem
-- statement:
--   Let $\mathbf{f}$ be a $C'$-mapping of an open set $E \subseteq \mathbb{R}^{n+m}$ into $\mathbb{R}^n$ with $\mathbf{f}(\mathbf{a},\mathbf{b}) = 0$, and suppose the partial derivative $A_x$ of $\mathbf{f}$ with respect to the first $n$ variables at $(\mathbf{a},\mathbf{b})$ is invertible. Then there are open sets $U \ni (\mathbf{a},\mathbf{b})$ and $W \ni \mathbf{b}$ and a $C'$-mapping $\mathbf{g} : W \to \mathbb{R}^n$ with $\mathbf{g}(\mathbf{b}) = \mathbf{a}$, such that for each $\mathbf{y} \in W$ the point $(\mathbf{g}(\mathbf{y}),\mathbf{y})$ lies in $U$ and satisfies $\mathbf{f} = 0$, and is the only point of $U$ over $\mathbf{y}$ that does.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 9, p. 224, Theorem 9.28

import Mathlib

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 9.28 (implicit function theorem): let `f` be a `C'`-mapping of an open set
`E ⊆ ℝⁿ × ℝᵐ` into `ℝⁿ` with `f (a, b) = 0`, and suppose the partial derivative of `f` in the
first group of variables at `(a, b)` is invertible.  Then there are open sets `U ∋ (a, b)` and
`W ∋ b` and a `C'`-mapping `g : W → ℝⁿ` with `g b = a` such that for `y ∈ W` the point
`(g y, y)` lies in `U` and solves `f (x, y) = 0`, and it is the only solution in `U`. -/
theorem ch09_implicit_function (n m : ℕ)
    (E : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m))) (hE : IsOpen E)
    (f : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n))
    (hf : ContDiffOn ℝ 1 f E)
    (a : EuclideanSpace ℝ (Fin n)) (b : EuclideanSpace ℝ (Fin m)) (hab : (a, b) ∈ E)
    (hfab : f (a, b) = 0)
    (A : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : HasFDerivAt f A (a, b))
    (hAx : Function.Bijective fun h : EuclideanSpace ℝ (Fin n) => A (h, 0)) :
    ∃ (U : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)))
      (W : Set (EuclideanSpace ℝ (Fin m)))
      (g : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)),
      IsOpen U ∧ IsOpen W ∧ (a, b) ∈ U ∧ U ⊆ E ∧ b ∈ W ∧ ContDiffOn ℝ 1 g W ∧ g b = a ∧
        ∀ y ∈ W, (g y, y) ∈ U ∧ f (g y, y) = 0 ∧
          ∀ x : EuclideanSpace ℝ (Fin n), (x, y) ∈ U → f (x, y) = 0 → x = g y := by sorry

end Rudin
