-- Prove2me | Theorems.Thm_ShorNonsmooth_Subdiff_dirDeriv_eq_max_subgradient
-- name    : ShorNonsmooth.Subdiff.dirDeriv_eq_max_subgradient
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T15:18:08.393241+00:00
-- url     : https://prove2.me/theorems/1ad7b3c1-fe86-4cba-946c-1841cac85d36
-- title:
--   Theorem 1.8 — $f'_\eta(x_0) = \max_{g \in G(x_0)} (g,\eta)$
-- statement:
--   Let $M \subseteq E_n$, let $f$ be convex on $M$, and let $x_0$ be an interior point of $M$. Then for every direction $\eta \in E_n$ the one-sided directional derivative $f'_\eta(x_0) = \lim_{t\to 0+} (f(x_0+t\eta) - f(x_0))/t$ exists and is finite, and
--
--   $$
--   f'_\eta(x_0) = \max_{g \in G(x_0)} (g, \eta),
--   $$
--
--   where $G(x_0)$ is the subdifferential of $f$ at $x_0$ and the maximum is attained.
--
--   This max formula identifies the directional derivative with the support function of the subdifferential; it is the main tool for computing subdifferentials of composite functions.
--
--   **Formalization Note** The conclusion is that some real $d$ is the right-hand limit and is the greatest element of $\{(g,\eta) : g \in G(x_0)\}$ (`IsGreatest`), so the maximum is attained and no `sSup` junk value can enter.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 9, Theorem 1.8 (formula (1.5))

import Mathlib
import Definitions.Def_ShorNonsmooth_Subdiff_Subdifferential
import Definitions.Def_ShorNonsmooth_Subdiff_DirDeriv

namespace ShorNonsmooth.Subdiff

/-- Shor (1985), p. 9, Theorem 1.8 (formula (1.5)): a convex function `f` with domain `M` has, at
every interior point `x₀` of `M` and in every direction `η`, a (finite, one-sided) directional
derivative `f′_η(x₀)`, and `f′_η(x₀) = max_{g ∈ G(x₀)} (g, η)`, the maximum being attained. -/
theorem dirDeriv_eq_max_subgradient {n : ℕ}
    (M : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ M f) (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ interior M)
    (η : EuclideanSpace ℝ (Fin n)) :
    ∃ d : ℝ, HasOneSidedDirDeriv f x₀ η d ∧
      IsGreatest ((fun g => inner ℝ g η) '' subdifferential M f x₀) d := by sorry

end ShorNonsmooth.Subdiff
