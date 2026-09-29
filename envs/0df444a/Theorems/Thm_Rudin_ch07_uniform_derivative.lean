-- Prove2me | Theorems.Thm_Rudin_ch07_uniform_derivative
-- name    : Rudin.ch07_uniform_derivative
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T23:23:20.872738+00:00
-- url     : https://prove2.me/theorems/46f55d01-e567-43f6-9ae3-7a5c4af08b75
-- title:
--   Theorem 7.17 — uniform convergence and differentiation
-- statement:
--   Let $f_n$ be differentiable on $[a,b]$, suppose $\{f_n(x_0)\}$ converges for some $x_0 \in [a,b]$, and suppose $\{f_n'\}$ converges uniformly on $[a,b]$. Then $\{f_n\}$ converges uniformly on $[a,b]$ to a function $g$, and $g'(x) = \lim_n f_n'(x)$ for every $x \in [a,b]$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 7, p. 152, Theorem 7.17

import Mathlib

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 7.17: let `f n` be differentiable on `[a, b]`, suppose `f n x₀` converges
for some `x₀ ∈ [a, b]`, and suppose the derivatives converge uniformly on `[a, b]`.  Then
`f n` converges uniformly on `[a, b]` to a function `g` whose derivative at each point is the
limit of the derivatives. -/
theorem ch07_uniform_derivative (a b : ℝ) (hab : a < b) (f : ℕ → ℝ → ℝ) (f' : ℕ → ℝ → ℝ)
    (hdiff : ∀ n, ∀ x ∈ Set.Icc a b, HasDerivAt (f n) (f' n x) x)
    (x₀ : ℝ) (hx₀ : x₀ ∈ Set.Icc a b) (hconv : ∃ c : ℝ, Tendsto (fun n => f n x₀) atTop (𝓝 c))
    (h' : ∃ h : ℝ → ℝ, TendstoUniformlyOn f' h atTop (Set.Icc a b)) :
    ∃ g : ℝ → ℝ, ∃ h : ℝ → ℝ,
      TendstoUniformlyOn f g atTop (Set.Icc a b) ∧
      TendstoUniformlyOn f' h atTop (Set.Icc a b) ∧
      ∀ x ∈ Set.Icc a b, HasDerivAt g (h x) x := by sorry

end Rudin
