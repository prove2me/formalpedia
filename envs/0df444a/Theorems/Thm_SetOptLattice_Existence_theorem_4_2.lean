-- Prove2me | Theorems.Thm_SetOptLattice_Existence_theorem_4_2
-- name    : SetOptLattice.Existence.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:20:50.162052+00:00
-- url     : https://prove2.me/theorems/a8c3e69e-7288-421e-8767-3fc782285e57
-- title:
--   Theorem 4.2, p. 23 — lsc ψ△∘f with a compact sublevel set above the infimum: each ψ△∘f attains, attainers form a (0,Ψ)-solution
-- statement:
--   Let $X$ be a separated topological linear space over $\mathbb R$, $(Z,\preceq)$ a preordered set, $\Psi$ a non-empty family of monotone functions $\psi\colon Z\to\overline{\mathbb R}$ and $f\colon X\to\mathcal P(Z,\Psi)$. Assume that for each $\psi\in\Psi$ the function $\psi^\triangle\circ f\colon X\to\overline{\mathbb R}$ is lower semicontinuous and there is $r_\psi\in\mathbb R$ with $\inf(\psi^\triangle\circ f)[X]<r_\psi$ such that the sublevel set $L_{\psi^\triangle\circ f}(r_\psi)$ is compact. Then:
--
--   1. for each $\psi\in\Psi$ there is $x_\psi\in X$ with
--   $$(\psi^\triangle\circ f)(x_\psi)=\inf(\psi^\triangle\circ f)[X]; \tag{4.1}$$
--   2. the set $\{x_\psi\in X\mid x_\psi\text{ satisfies (4.1)},\ \psi\in\Psi\}$, i.e. the set of all $x\in X$ that satisfy (4.1) for some $\psi\in\Psi$, is a $(0,\Psi)$-solution of (P).
--
--   This is the basic Weierstrass-type existence theorem for set optimization: attainment of every scalarized infimum yields an exact solution in the sense of Definition 3.7.
--
--   **Formalization Note** $\Psi\neq\emptyset$ is added: for $\Psi=\emptyset$ the set in item 2 is empty, while a solution is non-empty by definition. The set in item 2 is read as the set of all points attaining the infimum of some $\psi^\triangle\circ f$, $\psi\in\Psi$; the infimum $\inf(\psi^\triangle\circ f)[X]$ is the scalar infimum over $X$ in $\overline{\mathbb R}$.
-- source:
--   Crespi, Hamel, Rocca, Schrage, arXiv:1812.03300v1, p. 23, Theorem 4.2, (4.1); standing assumption of §4, p. 22

import Mathlib
import Definitions.Def_SetOptLattice_Existence_Model

namespace SetOptLattice.Existence

open Set Filter Topology
open scoped Pointwise

/-- Theorem 4.2, p. 23. -/
theorem theorem_4_2 {X Z : Type*} [Preorder Z]
    [AddCommGroup X] [Module ℝ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [ContinuousSMul ℝ X] [T2Space X]
    (Ψ : Set (Z → EReal)) (hΨ : ∀ ψ ∈ Ψ, Monotone ψ) (hΨne : Ψ.Nonempty)
    (f : X → Set Z) (hf : ∀ x, IsPsiClosed Ψ (f x))
    (hlsc : ∀ ψ ∈ Ψ, LowerSemicontinuous (fun x => infExt ψ (f x)))
    (hr : ∀ ψ ∈ Ψ, ∃ r : ℝ, (⨅ x, infExt ψ (f x)) < (r : EReal) ∧
      IsCompact (sublevel (fun x => infExt ψ (f x)) r)) :
    (∀ ψ ∈ Ψ, ∃ xψ : X, infExt ψ (f xψ) = ⨅ x, infExt ψ (f x)) ∧
      IsSolution Ψ f 0 {xψ : X | ∃ ψ ∈ Ψ, infExt ψ (f xψ) = ⨅ x, infExt ψ (f x)} := by sorry

end SetOptLattice.Existence
