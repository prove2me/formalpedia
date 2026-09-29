-- Prove2me | Theorems.Thm_Rudin_ch06_integration_by_parts
-- name    : Rudin.ch06_integration_by_parts
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-09-12T23:40:01.586289+00:00
-- url     : https://prove2.me/theorems/d3bd9390-7a98-4982-a0ed-250c9f6c31a7
-- title:
--   Theorem 6.22 — integration by parts
-- statement:
--   If $F$ and $G$ are differentiable on $[a,b]$ with $F' = f \in \mathcal{R}$ and $G' = g \in \mathcal{R}$, then $$\int_a^b F(x)g(x)\,dx = F(b)G(b) - F(a)G(a) - \int_a^b f(x)G(x)\,dx .$$
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 6, p. 134, Theorem 6.22

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 6.22 (integration by parts): if `F` and `G` are differentiable on `[a, b]`
with `F' = f ∈ ℛ` and `G' = g ∈ ℛ`, then
`∫ₐᵇ F g dx = F b G b - F a G a - ∫ₐᵇ f G dx`. -/
theorem ch06_integration_by_parts (a b : ℝ) (hab : a ≤ b) (F G f g : ℝ → ℝ)
    (hF : ∀ x ∈ Set.Icc a b, HasDerivAt F (f x) x)
    (hG : ∀ x ∈ Set.Icc a b, HasDerivAt G (g x) x)
    (hf : RiemannIntegrable a b f) (hg : RiemannIntegrable a b g) :
    RiemannIntegral a b (fun x => F x * g x) =
      F b * G b - F a * G a - RiemannIntegral a b (fun x => f x * G x) := by sorry

end Rudin
