-- Prove2me | Theorems.Thm_ShorNonsmooth_Subdiff_max_function_subgradient
-- name    : ShorNonsmooth.Subdiff.max_function_subgradient
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T15:37:23.969545+00:00
-- url     : https://prove2.me/theorems/614c03fd-585c-4fed-b3a9-a8a5cc6d3fc9
-- title:
--   Theorem 1.13 — a max of convex functions is convex and contains the active subgradients
-- statement:
--   Let $f_1, \dots, f_m$ ($m \ge 1$) be convex functions on $E_n$ and let
--
--   $$
--   \varphi(x) = \max_{1 \le i \le m} f_i(x).
--   $$
--
--   Then $\varphi$ is convex, and at every point $x_0$ the subdifferential of $\varphi$ contains every subgradient $g_{f_i}(x_0) \in G_{f_i}(x_0)$ for each active index $i \in I(x_0) = \{i : \varphi(x_0) = f_i(x_0)\}$.
--
--   This gives the standard rule for computing a subgradient of a max function: evaluate any active piece and take one of its subgradients.
--
--   **Formalization Note** Only the inclusion $G_{f_i}(x_0) \subseteq G_\varphi(x_0)$ for active $i$ is asserted, as in the book. The maximum is `Finset.sup'` over `Fin m`, which requires $m \ge 1$ (the book's maximum over $\{1,\dots,m\}$ presupposes it).
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 14, Theorem 1.13

import Mathlib
import Definitions.Def_ShorNonsmooth_Subdiff_Subdifferential

namespace ShorNonsmooth.Subdiff

/-- Shor (1985), p. 14, Theorem 1.13: let `f₁, …, f_m` (`m ≥ 1`) be convex functions on `E_n` and
`φ(x) = max_{i ∈ 1..m} f_i(x)`. Then `φ` is convex, and at every point `x₀` the subdifferential of
`φ` contains every subgradient of `f_i` at `x₀` for each active index `i ∈ I(x₀)`, where
`I(x₀) = {i : φ(x₀) = f_i(x₀)}`. Only this inclusion is asserted, as in the book. -/
theorem max_function_subgradient {n m : ℕ} (hm : 0 < m)
    (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (hf : ∀ i, ConvexOn ℝ Set.univ (f i)) :
    ConvexOn ℝ Set.univ
        (fun x => Finset.univ.sup' ⟨⟨0, hm⟩, Finset.mem_univ _⟩ (fun i => f i x)) ∧
      ∀ (x₀ : EuclideanSpace ℝ (Fin n)) (i : Fin m),
        Finset.univ.sup' ⟨⟨0, hm⟩, Finset.mem_univ _⟩ (fun j => f j x₀) = f i x₀ →
          subdifferential Set.univ (f i) x₀ ⊆
            subdifferential Set.univ
              (fun x => Finset.univ.sup' ⟨⟨0, hm⟩, Finset.mem_univ _⟩ (fun j => f j x)) x₀ := by sorry

end ShorNonsmooth.Subdiff
