-- Prove2me | Theorems.Thm_ShorNonsmooth_Subdiff_subdifferential_nonneg_combination
-- name    : ShorNonsmooth.Subdiff.subdifferential_nonneg_combination
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T15:42:56.245637+00:00
-- url     : https://prove2.me/theorems/109614b1-87aa-4e8f-a8a1-13f353028069
-- title:
--   Theorem 1.12 — the subdifferential of $\sum a_i f_i$ ($a_i \ge 0$) is $\sum a_i G_{f_i}(x_0)$
-- statement:
--   Let $f_1, \dots, f_k$ be convex functions on $E_n$, let $a_1, \dots, a_k \ge 0$, and let
--
--   $$
--   f(x) = \sum_{i=1}^k a_i f_i(x).
--   $$
--
--   Then $f$ is convex, and for every point $x_0$ its subdifferential consists of exactly the vectors of the form
--
--   $$
--   g(x_0) = \sum_{i=1}^k a_i g_i(x_0), \qquad g_i(x_0) \in G_{f_i}(x_0),
--   $$
--
--   i.e. $G_f(x_0) = \{\sum_{i=1}^k a_i g_i : g_i \in G_{f_i}(x_0),\ i = 1,\dots,k\}$.
--
--   This is the sum rule (Moreau–Rockafellar) for finite-valued convex functions on $E_n$: every subgradient of a nonnegative combination is obtained by combining subgradients of the pieces.
--
--   **Formalization Note** The conclusion is an equality of sets, both inclusions. The index set is `Fin k`; for $k = 0$ the function is $0$ and both sides are $\{0\}$. The book prints $g_i(x_0) \in G_{f_i}(x)$, a misprint for $G_{f_i}(x_0)$.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 13, Theorem 1.12 (formula (1.7))

import Mathlib
import Definitions.Def_ShorNonsmooth_Subdiff_Subdifferential

namespace ShorNonsmooth.Subdiff

/-- Shor (1985), p. 13, Theorem 1.12: let `f(x) = ∑_{i=1}^k a_i f_i(x)` with `a_i ≥ 0` and each
`f_i` convex on `E_n`. Then `f` is convex, and its subdifferential at any point `x₀` consists of
exactly the vectors `∑_{i=1}^k a_i g_i` with `g_i ∈ G_{f_i}(x₀)` (formula (1.7); the book prints
`G_{f_i}(x)` for `G_{f_i}(x₀)`). -/
theorem subdifferential_nonneg_combination {n k : ℕ} (a : Fin k → ℝ) (ha : ∀ i, 0 ≤ a i)
    (f : Fin k → EuclideanSpace ℝ (Fin n) → ℝ) (hf : ∀ i, ConvexOn ℝ Set.univ (f i)) :
    ConvexOn ℝ Set.univ (fun x => ∑ i, a i * f i x) ∧
      ∀ x₀ : EuclideanSpace ℝ (Fin n),
        subdifferential Set.univ (fun x => ∑ i, a i * f i x) x₀ =
          {g | ∃ gs : Fin k → EuclideanSpace ℝ (Fin n),
            (∀ i, gs i ∈ subdifferential Set.univ (f i) x₀) ∧ g = ∑ i, a i • gs i} := by sorry

end ShorNonsmooth.Subdiff
