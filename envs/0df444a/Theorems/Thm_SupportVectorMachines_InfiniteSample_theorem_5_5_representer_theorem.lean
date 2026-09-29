-- Prove2me | Theorems.Thm_SupportVectorMachines_InfiniteSample_theorem_5_5_representer_theorem
-- name    : SupportVectorMachines.InfiniteSample.theorem_5_5_representer_theorem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T23:06:57.470755+00:00
-- url     : https://prove2.me/theorems/ae73c7eb-449e-40fc-9c30-1f8829c6931e
-- title:
--   Theorem 5.5 — the representer theorem for empirical SVM solutions
-- statement:
--   This is Theorem 5.5 (the **representer theorem**) of Steinwart & Christmann, *Support Vector
--   Machines* (Springer 2008, p. 168): let $L : X \times Y \times \mathbb R \to [0,\infty)$ be a
--   convex loss and $D := ((x_1,y_1),\dots,(x_n,y_n)) \in (X \times Y)^n$. Let $H$ be an RKHS over
--   $X$ with kernel $k$. Then, for all $\lambda > 0$, there exists a unique **empirical SVM
--   solution** $f_{D,\lambda} \in H$, i.e. a unique minimizer of
--
--   $$
--   f \mapsto \lambda\|f\|_H^2 + R_{L,D}(f)
--   $$
--
--   over $H$. In addition, there exist $\alpha_1,\dots,\alpha_n \in \mathbb R$ such that
--
--   $$
--   f_{D,\lambda}(x) = \sum_{i=1}^n \alpha_i\, k(x,x_i) \qquad \text{for all } x \in X.
--   $$
--
--   This is the single most quoted structural fact about support vector machines: although the
--   optimization problem ranges over the entire (typically infinite-dimensional) RKHS $H$, its
--   minimizer always lies in the $n$-dimensional subspace spanned by the kernel functions
--   $k(\cdot,x_1),\dots,k(\cdot,x_n)$, which is exactly what makes SVM training a finite-dimensional
--   (and hence computationally tractable) problem in practice.
--
--   **Formalization Note** The goal keeps both of the theorem's clauses together, as a single
--   unique witness: existence and uniqueness of the minimizer, and — for that same, unique
--   minimizer — the finite kernel-expansion representation. The coefficients $\alpha_1,\dots,
--   \alpha_n$ are only asserted to exist, not to be unique, matching the book exactly (the
--   representation can be non-unique when the $k(\cdot,x_i)$ are linearly dependent). $H$ is
--   required to carry a genuine reproducing kernel $k$ (`IsRKHSOfKernel`), not merely to be an
--   abstract Hilbert space, since the representation clause is stated directly in terms of $k$.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, p. 168, Theorem 5.5

import Mathlib
import Definitions.Def_SupportVectorMachines_InfiniteSample_Loss
import Definitions.Def_SupportVectorMachines_InfiniteSample_IsRKHSOfKernel
import Definitions.Def_SupportVectorMachines_InfiniteSample_populationRisk

open MeasureTheory

namespace SupportVectorMachines.InfiniteSample

/-- Theorem 5.5 (Representer theorem), p. 168: let `L` be a convex loss and
`D := ((x₁,y₁),…,(xₙ,yₙ)) ∈ (X × ℝ)ⁿ`. Let `H` be the RKHS of a kernel `k` over `X`. Then for all
`λ > 0` there exists a unique empirical SVM solution `f_{D,λ} ∈ H`, i.e. a unique minimizer of
`f ↦ λ‖f‖²_H + R_{L,D}(f)` over `H`; moreover there exist `α₁,…,αₙ ∈ ℝ` with
`f_{D,λ}(x) = ∑ᵢ αᵢ k(x,xᵢ)` for all `x ∈ X`. -/
theorem theorem_5_5_representer_theorem {X : Type*} {n : ℕ} (hn : 0 < n)
    (L : Loss X) (hL : ∀ x y, ConvexOn ℝ Set.univ (L x y)) (hLnn : ∀ x y t, 0 ≤ L x y t)
    (D : Fin n → X × ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (toFun : H →ₗ[ℝ] (X → ℝ)) (k : X → X → ℝ) (hRKHS : IsRKHSOfKernel H toFun k)
    (lam : ℝ) (hlam : 0 < lam) :
    ∃! f : H,
      (∀ g : H, lam * ‖f‖ ^ 2 + empiricalRisk n L D (toFun f) ≤
        lam * ‖g‖ ^ 2 + empiricalRisk n L D (toFun g)) ∧
      ∃ α : Fin n → ℝ, ∀ x : X, toFun f x = ∑ i, α i * k x (D i).1 := by sorry

end SupportVectorMachines.InfiniteSample
