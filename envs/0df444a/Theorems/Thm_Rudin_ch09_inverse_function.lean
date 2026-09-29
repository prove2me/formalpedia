-- Prove2me | Theorems.Thm_Rudin_ch09_inverse_function
-- name    : Rudin.ch09_inverse_function
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T02:25:45.947485+00:00
-- url     : https://prove2.me/theorems/70a6a30b-c3e6-4746-9369-6c60672c09dc
-- title:
--   Theorem 9.24 — inverse function theorem
-- statement:
--   Let $\mathbf{f}$ be a $C'$-mapping of an open set $E \subseteq \mathbb{R}^n$ into $\mathbb{R}^n$ and suppose $\mathbf{f}'(\mathbf{a})$ is invertible for some $\mathbf{a} \in E$. Then there exist open sets $U$ and $V$ with $\mathbf{a} \in U \subseteq E$ and $\mathbf{f}(\mathbf{a}) \in V$ such that $\mathbf{f}$ is one-to-one on $U$ and $\mathbf{f}(U) = V$; moreover the inverse mapping $\mathbf{g}$, defined on $V$ by $\mathbf{g}(\mathbf{f}(\mathbf{x})) = \mathbf{x}$, is a $C'$-mapping on $V$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 9, p. 221, Theorem 9.24

import Mathlib

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 9.24 (inverse function theorem): let `f` be a `C'`-mapping of an open set
`E ⊆ ℝⁿ` into `ℝⁿ` whose derivative at `a ∈ E` is invertible.  Then there are open sets
`U ∋ a` and `V ∋ f a` such that `f` is one-to-one on `U` with `f(U) = V`, and the inverse
mapping `g` of `f` restricted to `U` is a `C'`-mapping on `V`. -/
theorem ch09_inverse_function (n : ℕ) (E : Set (EuclideanSpace ℝ (Fin n))) (hE : IsOpen E)
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hf : ContDiffOn ℝ 1 f E)
    (a : EuclideanSpace ℝ (Fin n)) (ha : a ∈ E)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hA : HasFDerivAt f A a)
    (hAinv : Function.Bijective A) :
    ∃ (U V : Set (EuclideanSpace ℝ (Fin n)))
      (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      IsOpen U ∧ IsOpen V ∧ a ∈ U ∧ U ⊆ E ∧ f a ∈ V ∧ Set.InjOn f U ∧ f '' U = V ∧
        (∀ x ∈ U, g (f x) = x) ∧ (∀ y ∈ V, f (g y) = y) ∧ ContDiffOn ℝ 1 g V := by sorry

end Rudin
