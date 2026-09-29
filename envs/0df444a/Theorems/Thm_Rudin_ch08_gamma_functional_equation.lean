-- Prove2me | Theorems.Thm_Rudin_ch08_gamma_functional_equation
-- name    : Rudin.ch08_gamma_functional_equation
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T02:29:48.392335+00:00
-- url     : https://prove2.me/theorems/57f8ccef-a33d-4421-90d5-dbf43f7c4d19
-- title:
--   Theorem 8.18 — functional equation and log-convexity of $\Gamma$
-- statement:
--   For $x > 0$, $\Gamma(x+1) = x\Gamma(x)$; $\Gamma(n+1) = n!$ for nonnegative integers $n$; and $\log \Gamma$ is convex on $(0,\infty)$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 8, pp. 192-193, Definition 8.17 and Theorem 8.18

import Mathlib
import Definitions.Def_Rudin_ch08_fourier

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 8.18: the Gamma function satisfies `Γ(x+1) = x Γ(x)` for `x > 0`,
`Γ(n+1) = n!` for nonnegative integers `n`, and `log Γ` is convex on `(0, ∞)`. -/
theorem ch08_gamma_functional_equation :
    (∀ x : ℝ, 0 < x → Real.Gamma (x + 1) = x * Real.Gamma x) ∧
    (∀ n : ℕ, Real.Gamma (n + 1) = n.factorial) ∧
    ConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun x => Real.log (Real.Gamma x)) := by sorry

end Rudin
