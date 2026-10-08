-- Prove2me | Theorems.Thm_ShorNonsmooth_LinearRate_linear_rate_of_angle_condition_along_iterates
-- name    : ShorNonsmooth.LinearRate.linear_rate_of_angle_condition_along_iterates
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T12:03:15.11377+00:00
-- url     : https://prove2.me/theorems/6f3e1153-cc7b-434d-b90f-5e25ca88b941
-- title:
--   Remark after Theorem 2.7 — (2.12) is needed only at the iterates $x_k$
-- statement:
--   Under the data of Theorem 2.7 — $f$ convex on $E_n$ with nonempty set of minima, $x^*(x)$ the nearest minimum point, $0 \le \varphi < \pi/2$, $h_1$ chosen by (2.13)/(2.14), $h_{k+1} = h_k r(\varphi)$ for $k \ge 1$, and the normalized subgradient iterates $x_k$ — assume the angle condition only along the sequence:
--   $$
--   (g_f(x_k),\, x_k - x^*(x_k)) \ge \cos\varphi\, \|g_f(x_k)\|\, \|x_k - x^*(x_k)\|, \qquad k = 0, 1, 2, \dots
--   $$
--   Then the conclusions (2.18)/(2.19) of Theorem 2.7 still hold for all $k$:
--   $$
--   \|x_k - x^*(x_k)\| \le h_{k+1}/\cos\varphi \ (\pi/4 \le \varphi), \qquad \|x_k - x^*(x_k)\| \le 2h_{k+1}\cos\varphi \ (\varphi < \pi/4).
--   $$
--
--   This is the form in which Theorem 2.7 is applied in the proof of Theorem 2.8, where the angle condition is only known inside a ball around the minimum.
--
--   **Formalization Note** As in Theorem 2.7, the method stops and stays at a point with $g_f(x_k) = 0$, and the bound is asserted for all $k$.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 32, Remark after Theorem 2.7

import Mathlib
import Definitions.Def_ShorNonsmooth_LinearRate_SubgradientMethod

namespace ShorNonsmooth.LinearRate

/-- Shor (1985), p. 32, **Remark** after Theorem 2.7: the theorem remains valid if (2.12)
holds only for the points of the sequence `{x_k}`. Same data and conclusions as Theorem 2.7,
with the angle condition (2.12) required only at the iterates `x_k`, `k = 0, 1, 2, …`. -/
theorem linear_rate_of_angle_condition_along_iterates {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (hMne : (ShorNonsmooth.SubgradMethod.MinSet f).Nonempty)
    (φ : ℝ) (hφ0 : 0 ≤ φ) (hφ1 : φ < Real.pi / 2)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x, ShorNonsmooth.AlmostDiff.IsSubgradient f x (g x))
    (x₀ : EuclideanSpace ℝ (Fin n)) (h : ℕ → ℝ)
    (hangle : ∀ k, inner ℝ (g (ShorNonsmooth.SubgradMethod.normalizedIter g h x₀ k))
        (ShorNonsmooth.SubgradMethod.normalizedIter g h x₀ k - nearestMin f (ShorNonsmooth.SubgradMethod.normalizedIter g h x₀ k)) ≥
      Real.cos φ * ‖g (ShorNonsmooth.SubgradMethod.normalizedIter g h x₀ k)‖ *
        ‖ShorNonsmooth.SubgradMethod.normalizedIter g h x₀ k - nearestMin f (ShorNonsmooth.SubgradMethod.normalizedIter g h x₀ k)‖)
    (hh₁_ge : Real.pi / 4 ≤ φ → ‖nearestMin f x₀ - x₀‖ * Real.cos φ ≤ h 1)
    (hh₁_lt : φ < Real.pi / 4 → ‖nearestMin f x₀ - x₀‖ / (2 * Real.cos φ) ≤ h 1)
    (hrec : ∀ k, 1 ≤ k → h (k + 1) = h k * stepRatio φ) :
    (Real.pi / 4 ≤ φ → ∀ k, ‖ShorNonsmooth.SubgradMethod.normalizedIter g h x₀ k - nearestMin f (ShorNonsmooth.SubgradMethod.normalizedIter g h x₀ k)‖
        ≤ h (k + 1) / Real.cos φ) ∧
    (φ < Real.pi / 4 → ∀ k, ‖ShorNonsmooth.SubgradMethod.normalizedIter g h x₀ k - nearestMin f (ShorNonsmooth.SubgradMethod.normalizedIter g h x₀ k)‖
        ≤ 2 * h (k + 1) * Real.cos φ) := by sorry

end ShorNonsmooth.LinearRate
