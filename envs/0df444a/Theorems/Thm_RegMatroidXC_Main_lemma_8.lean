-- Prove2me | Theorems.Thm_RegMatroidXC_Main_lemma_8
-- name    : RegMatroidXC.Main.lemma_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T16:16:41.813934+00:00
-- url     : https://prove2.me/theorems/2b62d60d-094c-4e03-a0a7-9de7bf17468c
-- title:
--   Lemma 8 — for convex f on [a, b] and ε ∈ [0, b − a], f(a + ε) + f(b − ε) ≤ f(a) + f(b)
-- statement:
--   Let $f : [a, b] \to \mathbb R$ be convex. For every $\varepsilon \in [0, b - a]$,
--   $$f(a + \varepsilon) + f(b - \varepsilon) \le f(a) + f(b).$$
--
--   The proof of the main theorem applies this to $f(x) = x^6$ to push the sizes of the parts of a decomposition to the extremes.
--
--   **Formalization Note** $f$ is a function on $\mathbb R$ that is assumed convex on $[a, b]$ only; its values outside $[a, b]$ play no role.
-- source:
--   Aprile & Fiorini, Regular Matroids Have Polynomial Extension Complexity, arXiv:1909.08539v2, p. 3, Lemma 8

import Mathlib

namespace RegMatroidXC.Main

theorem lemma_8 (f : ℝ → ℝ) (a b : ℝ) (hf : ConvexOn ℝ (Set.Icc a b) f) (ε : ℝ)
    (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ b - a) :
    f (a + ε) + f (b - ε) ≤ f a + f b := by sorry

end RegMatroidXC.Main
