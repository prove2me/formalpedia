-- Prove2me | Theorems.Thm_SAGFiniteSum_Rate_centered_init_norm_bound
-- name    : SAGFiniteSum.Rate.centered_init_norm_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:17:48.890029+00:00
-- url     : https://prove2.me/theorems/65d6cc59-3f5b-4f23-8030-0bcc175186cf
-- title:
--   App. B.8.2, p. 48 — centered table: ‖y⁰ − f′(x*)‖² ≤ 8nL(g(x⁰) − g(x*))
-- statement:
--   Assume the standing assumptions of §3. Let $y^0_i=f'_i(x^0)-g'(x^0)$ be the centered initial table. Then
--   $$
--   \|y^0-f'(x^*)\|^2=\sum_{i=1}^n\big\|y^0_i-f'_i(x^*)\big\|^2\ \le\ 8nL\big(g(x^0)-g(x^*)\big).
--   $$
--
--   This bounds the table part of the Lyapunov function at the centered initialization.
--
--   **Formalization Note** The page's fourth line writes $(x_0-x^*)$ for $(x^0-x^*)$; the initial point is meant. $n\ge1$ suffices (no $n\ge2$). The inequality cited as "[Nesterov, 2004, Equations 2.17]" (Nesterov's (2.1.7)) is a consequence of convexity and $L$-Lipschitz gradients, both standing assumptions.
-- source:
--   Schmidt, Le Roux & Bach, arXiv:1309.2388v2, App. B.8.2, display on p. 48

import Mathlib
import Definitions.Def_SAGFiniteSum_Rate_Model

open scoped RealInnerProductSpace

namespace SAGFiniteSum.Rate

/-- B.8.2, norm bound (arXiv:1309.2388v2, p. 48). Under the standing assumptions, the centered
table `y⁰ᵢ = f'ᵢ(x⁰) − g'(x⁰)` satisfies
`‖y⁰ − f'(x*)‖² = ∑ᵢ ‖y⁰ᵢ − f'ᵢ(x*)‖² ≤ 8nL(g(x⁰) − g(x*))`. -/
theorem centered_init_norm_bound {p n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (L : ℝ)
    (xstar : EuclideanSpace ℝ (Fin p)) (hA : SAGAssumptions f f' L xstar)
    (x0 : EuclideanSpace ℝ (Fin p)) :
    ∑ i, ‖centeredTable f' x0 i - f' i xstar‖ ^ 2
      ≤ 8 * (n : ℝ) * L * (SAGA.Convex.fAvg f x0 - SAGA.Convex.fAvg f xstar) := by sorry

end SAGFiniteSum.Rate
