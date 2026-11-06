-- Prove2me | Theorems.Thm_TIESched_lemma_5_5
-- name    : TIESched.lemma_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:44:28.659208+00:00
-- url     : https://prove2.me/theorems/b412e919-3e4e-4453-8010-a1fb024ef9f8
-- title:
--   Lemma 5.5 — Markov–Kakutani fixed-point theorem
-- statement:
--   Let $K$ be a nonempty compact convex subset of a product $\mathbb R^\iota$ of real coordinate spaces (any index set $\iota$, product topology). Every family $\Phi$ of maps $K\to K$ that are continuous, affine on $K$ and pairwise commuting has a common fixed point: there is $x\in K$ with $f(x)=x$ for all $f\in\Phi$.
--
--   It yields the padding-invariant replacement of Lemma 5.6 and the invariant means of Lemma A.1.
--
--   Differences from the source:
--   - encoding: maps from K to itself → functions on ℝ^ι that map K into K, are continuous on K, preserve convex combinations of points of K and commute on K; reason: only their values on K matter; same class of maps
-- source:
--   Wang, Xu, Zhang, Tight Analysis of Randomized Truthful Scheduling: An (m+1)/2 Lower Bound, arXiv:2611.05142 (artifact sha256 a89db2da…), Lemma 5.5, p.23 (citing Kakutani 1938)

import Mathlib

set_option autoImplicit false

namespace TIESched

/-- **Lemma 5.5 (Markov–Kakutani fixed-point theorem)** (Wang, Xu, Zhang, arXiv:2611.05142,
Lemma 5.5, p.23, citing [Kak38]). Let `K` be a nonempty compact convex subset of a product of real
coordinate spaces. Every commuting family of continuous affine maps from `K` to itself has a common
fixed point.

**Formalization Note.** The product of real coordinate spaces is `ι → ℝ` with the product topology,
for an arbitrary (possibly uncountable) index type `ι`. A map of the family is a function on
`ι → ℝ` that maps `K` into `K`, is continuous on `K`, preserves convex combinations of points of `K`
(affine on `K`), and commutes on `K` with every other map of the family. -/
theorem lemma_5_5 {ι : Type*} (K : Set (ι → ℝ)) (hne : K.Nonempty) (hK : IsCompact K)
    (hconv : Convex ℝ K) (Φ : Set ((ι → ℝ) → ι → ℝ))
    (hmaps : ∀ f ∈ Φ, Set.MapsTo f K K) (hcont : ∀ f ∈ Φ, ContinuousOn f K)
    (haff : ∀ f ∈ Φ, ∀ x ∈ K, ∀ y ∈ K, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      f (t • x + (1 - t) • y) = t • f x + (1 - t) • f y)
    (hcomm : ∀ f ∈ Φ, ∀ g ∈ Φ, ∀ x ∈ K, f (g x) = g (f x)) :
    ∃ x ∈ K, ∀ f ∈ Φ, f x = x := by sorry

end TIESched
