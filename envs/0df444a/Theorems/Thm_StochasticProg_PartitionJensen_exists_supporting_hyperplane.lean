-- Prove2me | Theorems.Thm_StochasticProg_PartitionJensen_exists_supporting_hyperplane
-- name    : StochasticProg.PartitionJensen.exists_supporting_hyperplane
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:43:34.371045+00:00
-- url     : https://prove2.me/theorems/7612ed8f-6a5b-45a8-bfc5-0dc448bb48f8
-- title:
--   Supporting hyperplane of a convex function at a relative interior point of its domain (hint of Chapter 8, §8.2, Exercise 2)
-- statement:
--   Let $C \subseteq \mathbb R^N$ be convex, let $g : \mathbb R^N \to \mathbb R$ be convex on $C$, and let $\xi_0$ be a point of the relative interior of $C$. Then $g$ has a non-vertical supporting hyperplane at $(\xi_0, g(\xi_0))$ on $C$: there is a vector $a \in \mathbb R^N$ such that
--
--   $$
--   g(\xi_0) + \langle a, \xi - \xi_0 \rangle \;\le\; g(\xi) \qquad \text{for all } \xi \in C .
--   $$
--
--   Exercise 2 of §8.2 of Birge and Louveaux asks to prove Jensen's inequality $\mathrm E(g(\xi)) \ge g(\mathrm E(\xi))$ "by taking an expectation of the points on a supporting hyperplane to $g(\xi)$ at $g(\mathrm E(\xi))$". This statement is the existence of that hyperplane (the hint uses it at the mean $\mathrm E(\xi)$); for $C = \mathbb R^N$ it holds at every point.
--
--   **Formalization Note** $\mathbb R^N$ is `EuclideanSpace ℝ (Fin N)` with its inner product; the relative interior is Mathlib's `intrinsicInterior ℝ C`. No continuity or differentiability of $g$ is assumed.
--
--   Differences from the source:
--   - reading: g convex (the book's integrand of §8.2) → g : ℝ^N → ℝ real-valued and convex on a convex set C (values outside C unconstrained); reason: the book's convex functions may take the value +∞ (Section 2.11, printed p. 98, PDF p. 124); a proper convex function is finite and convex on C = dom g
--   - generalization: a supporting hyperplane at g(E(ξ)) → at (ξ₀, g(ξ₀)) for every ξ₀ in the relative interior of C, valid on C; reason: a non-vertical supporting hyperplane exists at every relative interior point and need not exist on the relative boundary; with C = ℝ^N it is every point, and ξ₀ = E(ξ) gives the hint's hyperplane
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, doi:10.1007/978-1-4614-0237-4, Chapter 8, §8.2, Exercise 2 (hint), printed p. 352 (PDF p. 371): "Prove Jensen's inequality, E(g(ξ)) ≥ g(E(ξ)), by taking an expectation of the points on a supporting hyperplane to g(ξ) at g(E(ξ))."

import Mathlib

namespace StochasticProg.PartitionJensen

/-- **Supporting hyperplane of a finite convex function on `ℝ^N`** (the object used in the hint
of §8.2 Exercise 2).
Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, Chapter 8,
§8.2, Exercise 2, printed p. 352 (PDF p. 371): "Prove Jensen's inequality, E(g(ξ)) ≥ g(E(ξ)),
by taking an expectation of the points on a supporting hyperplane to g(ξ) at g(E(ξ))."

A real-valued function `g` convex on a convex set `C ⊆ ℝ^N` has, at every point `ξ₀` of the
relative interior of `C`, an affine minorant on `C` that touches it at `ξ₀`: there is `a ∈ ℝ^N`
with `g ξ₀ + ⟨a, ξ - ξ₀⟩ ≤ g ξ` for all `ξ ∈ C`. For `C = ℝ^N` (relative interior `ℝ^N`) this
is a supporting hyperplane at every point.

**Formalization Note.** `ℝ^N` is `EuclideanSpace ℝ (Fin N)`; the relative interior is Mathlib's
`intrinsicInterior`. "Convex" is read as real-valued and convex on a convex set `C`, as for
Theorem 1 of §8.2; no continuity or differentiability is assumed. The hint applies the statement
at the mean `E(ξ)`; a non-vertical supporting hyperplane exists at every relative interior point
of `C` (and need not exist on its relative boundary), so `ξ₀` is any such point. -/
theorem exists_supporting_hyperplane {N : ℕ}
    (C : Set (EuclideanSpace ℝ (Fin N)))
    (g : EuclideanSpace ℝ (Fin N) → ℝ) (hg : ConvexOn ℝ C g)
    (ξ₀ : EuclideanSpace ℝ (Fin N)) (hξ₀ : ξ₀ ∈ intrinsicInterior ℝ C) :
    ∃ a : EuclideanSpace ℝ (Fin N), ∀ ξ ∈ C, g ξ₀ + inner ℝ a (ξ - ξ₀) ≤ g ξ := by sorry

end StochasticProg.PartitionJensen
