-- Prove2me | Theorems.Thm_SlowConvergence_Newton_psi_mem
-- name    : SlowConvergence.Newton.psi_mem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:39:56.412081+00:00
-- url     : https://prove2.me/theorems/4bc3dc47-724c-46af-900b-11d2c0cddf62
-- title:
--   §2, after (2.15), p. 4 — $|\psi_k| \in (0,1)$
-- statement:
--   Let $0 < \tau < 1$ and $\eta = \tau/(4-2\tau)$. For every $k \ge 0$ the number
--   $$\psi_k = \Big(\frac{k+1}{k+2}\Big)^{\frac12+\eta}$$
--   of (2.15) satisfies $|\psi_k| \in (0,1)$.
--
--   In the case $\alpha_k = 1$ used for the first coordinate of the Newton example, $\phi_k = -\psi_k$, so this gives $|\phi_k| \le 1$, the inequality the second-derivative bound (2.17) uses.
-- source:
--   Cartis, Gould & Toint, On the complexity of steepest descent, Newton's and regularized Newton's methods, preprint 15 Oct 2009, p. 4, §2, (2.15) and the sentence after it

import Mathlib
import Definitions.Def_SlowConvergence_Newton_Data
import Definitions.Def_SlowConvergence_Newton_Pieces

open scoped RealInnerProductSpace

namespace SlowConvergence.Newton

/-- Cartis, Gould & Toint, preprint 15 Oct 2009, §2, after (2.15), p. 4: "The definition of ψ_k implies
that |ψ_k| ∈ (0, 1) for all k ≥ 0", for `ψ_k = ((k+1)/(k+2))^{1/2+η}` and `η = τ/(4 − 2τ)`. -/
theorem psi_mem (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) (k : ℕ) :
    0 < |SlowConvergence.SteepestDescent.psi τ k| ∧ |SlowConvergence.SteepestDescent.psi τ k| < 1 := by sorry

end SlowConvergence.Newton
