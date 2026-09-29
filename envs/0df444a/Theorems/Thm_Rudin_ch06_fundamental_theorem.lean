-- Prove2me | Theorems.Thm_Rudin_ch06_fundamental_theorem
-- name    : Rudin.ch06_fundamental_theorem
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-09-12T23:52:46.816608+00:00
-- url     : https://prove2.me/theorems/83de4dfa-b930-4bb9-a286-079f5dd481a1
-- title:
--   Theorem 6.21 — the fundamental theorem of calculus
-- statement:
--   If $f \in \mathcal{R}$ on $[a,b]$ and there is a differentiable function $F$ on $[a,b]$ with $F' = f$, then $\int_a^b f(x)\,dx = F(b) - F(a)$. No continuity of $f$ is assumed: integrability plus the existence of an antiderivative suffices.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 6, p. 134, Theorem 6.21

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 6.21 (the fundamental theorem of calculus): if `f ∈ ℛ` on `[a, b]` and there
is a differentiable function `F` on `[a, b]` with `F' = f`, then
`∫ₐᵇ f dx = F b - F a`. -/
theorem ch06_fundamental_theorem (a b : ℝ) (hab : a ≤ b) (f F : ℝ → ℝ)
    (hf : RiemannIntegrable a b f)
    (hF : ∀ x ∈ Set.Icc a b, HasDerivAt F (f x) x) :
    RiemannIntegral a b f = F b - F a := by sorry

end Rudin
