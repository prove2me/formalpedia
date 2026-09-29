-- Prove2me | Theorems.Thm_Rudin_ch06_integral_derivative
-- name    : Rudin.ch06_integral_derivative
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T23:33:19.956541+00:00
-- url     : https://prove2.me/theorems/6dbc95f3-3475-4652-bab0-b591b9343186
-- title:
--   Theorem 6.20 — the integral as an antiderivative
-- statement:
--   Let $f \in \mathcal{R}$ on $[a,b]$ and put $F(x) = \int_a^x f(t)\,dt$. Then $F$ is continuous on $[a,b]$, and at every interior point $x_0$ where $f$ is continuous, $F$ is differentiable with $F'(x_0) = f(x_0)$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 6, p. 133, Theorem 6.20

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 6.20: if `f ∈ ℛ` on `[a, b]` and `F x = ∫ₐˣ f dt`, then `F` is continuous
on `[a, b]`; and if `f` is continuous at a point `x₀` of `[a, b]` then `F` is differentiable
at `x₀` with `F'(x₀) = f(x₀)`. -/
theorem ch06_integral_derivative (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℝ)
    (hf : RiemannIntegrable a b f) (hfb : ∃ M, ∀ x ∈ Set.Icc a b, |f x| ≤ M) :
    ContinuousOn (fun x => RiemannIntegral a x f) (Set.Icc a b) ∧
    ∀ x₀ ∈ Set.Ioo a b, ContinuousAt f x₀ →
      HasDerivAt (fun x => RiemannIntegral a x f) (f x₀) x₀ := by sorry

end Rudin
