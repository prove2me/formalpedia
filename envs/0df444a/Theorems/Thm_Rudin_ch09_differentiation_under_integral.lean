-- Prove2me | Theorems.Thm_Rudin_ch09_differentiation_under_integral
-- name    : Rudin.ch09_differentiation_under_integral
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-09-13T02:25:31.617259+00:00
-- url     : https://prove2.me/theorems/41e74cb0-05f9-491e-b786-2ebaa862e7f2
-- title:
--   Theorem 9.42 — differentiation under the integral sign
-- statement:
--   Let $\varphi(x,t)$ be defined for $x \in [a,b]$, $t \in [c,d]$, let $\alpha$ be increasing on $[a,b]$, let $\varphi(\cdot,t) \in \mathcal{R}(\alpha)$ for every $t$, and suppose that at $s \in (c,d)$ the partial derivative $D_2\varphi(x,t)$ exists and tends to $D_2\varphi(x,s)$ as $t \to s$, uniformly in $x$. Then $D_2\varphi(\cdot,s) \in \mathcal{R}(\alpha)$ and $f(t) = \int_a^b \varphi(x,t)\,d\alpha(x)$ satisfies $f'(s) = \int_a^b D_2\varphi(x,s)\,d\alpha(x)$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 9, p. 236, Theorem 9.42

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 9.42 (differentiation under the integral sign): let `φ x t` be defined for
`x ∈ [a, b]`, `t ∈ [c, d]`, let `α` increase on `[a, b]`, let `x ↦ φ x t` be integrable with
respect to `α` for each `t`, and suppose the `t`-derivative `D₂φ` exists and is continuous in
`t` at `s`, uniformly in `x`.  Then `x ↦ D₂φ x s` is integrable and the function
`f t = ∫ φ x t dα(x)` is differentiable at `s` with `f'(s) = ∫ D₂φ x s dα(x)`. -/
theorem ch09_differentiation_under_integral (a b c d : ℝ) (hab : a ≤ b) (hcd : c < d)
    (φ D2φ : ℝ → ℝ → ℝ) (α : ℝ → ℝ) (hα : MonotoneOn α (Set.Icc a b))
    (hint : ∀ t ∈ Set.Icc c d, RSIntegrable a b (fun x => φ x t) α)
    (hderiv : ∀ x ∈ Set.Icc a b, ∀ t ∈ Set.Ioo c d, HasDerivAt (fun u => φ x u) (D2φ x t) t)
    (s : ℝ) (hs : s ∈ Set.Ioo c d)
    (hunif : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Set.Icc a b, ∀ t ∈ Set.Ioo c d,
      |t - s| < δ → |D2φ x t - D2φ x s| < ε) :
    RSIntegrable a b (fun x => D2φ x s) α ∧
      HasDerivAt (fun t => RSIntegral a b (fun x => φ x t) α)
        (RSIntegral a b (fun x => D2φ x s) α) s := by sorry

end Rudin
