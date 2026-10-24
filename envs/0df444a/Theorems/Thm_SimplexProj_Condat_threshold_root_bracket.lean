-- Prove2me | Theorems.Thm_SimplexProj_Condat_threshold_root_bracket
-- name    : SimplexProj.Condat.threshold_root_bracket
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T23:23:07.72055+00:00
-- url     : https://prove2.me/theorems/b9f25f0e-638c-4ec9-b204-158a6dd56191
-- title:
--   Sect. 2 (p. 5) — $\tau$ is the root of $f(\rho)=\sum_n \max\{y_n-\rho,0\}-a$; sign test and bracket
-- statement:
--   Let $N \ge 1$, $a > 0$, $y \in \mathbb{R}^N$, let $x = P_\Delta(y)$ be the Euclidean projection of $y$ onto the simplex of radius $a$, and let $\tau$ be the threshold of Proposition 2.2, so $x_n = \max\{y_n - \tau, 0\}$ for all $n$. Let $y_{\max}$ and $y_{\min}$ be the largest and smallest entries of $y$ and define
--
--   $$f(\rho) := \sum_{n=1}^N \max\{y_n - \rho, 0\} - a \qquad (\rho \in \mathbb{R}).$$
--
--   Then: $f(\tau) = 0$; $f$ is convex; $f$ is piecewise linear with breakpoints at the $y_n$ (it is affine on every closed interval $[\rho_1, \rho_2]$ whose interior contains no $y_n$); $f$ is strictly decreasing on $(-\infty, y_{\max}]$ and $f(\rho) = -a$ for every $\rho \ge y_{\max}$; for every $\rho$, $f(\rho) < 0$ implies $\rho > \tau$ and $f(\rho) > 0$ implies $\rho < \tau$; $f(y_{\min} - a/N) \ge 0$, $f(y_{\max} - a/N) \le 0$ and $f(y_{\max} - a) \ge 0$; and consequently
--
--   $$\max\{y_{\max} - a,\ y_{\min} - a/N\} \le \tau \le y_{\max} - a/N.$$
--
--   These are the properties Condat lists in Sect. 2 when viewing the search for $\tau$ as root finding; the sign test is what lets an algorithm discard entries on one side of a trial value $\rho$.
--
--   **Formalization Note.** $f$, $y_{\max}$ and $y_{\min}$ are given as variables pinned by the hypotheses `hf`, `IsGreatest (Set.range y) ymax` and `IsLeast (Set.range y) ymin`. "Piecewise linear with breakpoints at the $y_n$" is rendered as: $f$ is affine on every interval $[\rho_1, \rho_2]$ with no $y_n$ in $(\rho_1, \rho_2)$.
-- source:
--   Condat, Fast Projection onto the Simplex and the ℓ1 Ball, HAL hal-01056171v2, p. 5, Sect. 2

import Mathlib
import Definitions.Def_SimplexProj_Condat_IsSimplexProjection

namespace SimplexProj.Condat

/-- Condat, Sect. 2, p. 5: with `f ρ = ∑ₙ max {y_n - ρ, 0} - a` and `τ` the threshold of
Proposition 2.2 (`x = P_Δ(y)`, `x_n = max {y_n - τ, 0}`): `τ` is a root of `f`; `f` is convex,
piecewise linear with breakpoints at the `y_n` (affine on every closed interval whose interior
contains no `y_n`), strictly decreasing on `(-∞, y_max]` and equal to `-a` on `[y_max, +∞)`;
`f ρ < 0 → ρ > τ` and `f ρ > 0 → ρ < τ`; `f (y_min - a/N) ≥ 0`, `f (y_max - a/N) ≤ 0`,
`f (y_max - a) ≥ 0`; hence `τ ∈ [max {y_max - a, y_min - a/N}, y_max - a/N]`.
Standing assumptions of p. 1: `N ≥ 1`, `a > 0`. -/
theorem threshold_root_bracket (N : ℕ) (hN : 1 ≤ N) (a : ℝ) (ha : 0 < a)
    (y x : Fin N → ℝ) (hx : IsSimplexProjection a y x)
    (τ : ℝ) (hτ : ∀ n, x n = max (y n - τ) 0)
    (f : ℝ → ℝ) (hf : ∀ ρ, f ρ = ∑ n, max (y n - ρ) 0 - a)
    (ymax ymin : ℝ) (hmax : IsGreatest (Set.range y) ymax) (hmin : IsLeast (Set.range y) ymin) :
    f τ = 0 ∧
    ConvexOn ℝ Set.univ f ∧
    (∀ ρ₁ ρ₂ : ℝ, ρ₁ ≤ ρ₂ → (∀ n, y n ∉ Set.Ioo ρ₁ ρ₂) →
      ∃ c d : ℝ, ∀ ρ ∈ Set.Icc ρ₁ ρ₂, f ρ = c * ρ + d) ∧
    StrictAntiOn f (Set.Iic ymax) ∧
    (∀ ρ ∈ Set.Ici ymax, f ρ = -a) ∧
    (∀ ρ : ℝ, f ρ < 0 → τ < ρ) ∧
    (∀ ρ : ℝ, 0 < f ρ → ρ < τ) ∧
    0 ≤ f (ymin - a / N) ∧ f (ymax - a / N) ≤ 0 ∧ 0 ≤ f (ymax - a) ∧
    max (ymax - a) (ymin - a / N) ≤ τ ∧ τ ≤ ymax - a / N := by sorry

end SimplexProj.Condat
