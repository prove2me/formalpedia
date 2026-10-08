-- Prove2me | Theorems.Thm_SlowConvergence_SteepestDescent_psi_mem
-- name    : SlowConvergence.SteepestDescent.psi_mem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:45:37.98304+00:00
-- url     : https://prove2.me/theorems/8646e07d-ff64-4dd0-a90b-452177b6b863
-- title:
--   §2 (2.15), p. 4 — $\psi_k \in (0,1)$ for all $k \ge 0$
-- statement:
--   Let $0 < \tau < 1$ and $\eta = \tau/(4-2\tau)$. For every $k \ge 0$ the number $\psi_k = \big(\tfrac{k+1}{k+2}\big)^{\frac12+\eta}$ of (2.15) satisfies
--   $$0 < \psi_k < 1.$$
--   The paper states this as $|\psi_k| \in (0,1)$; it controls the size of $\phi_k = (1-\alpha_k-\psi_k)/\alpha_k$ and hence of the coefficients (2.14).
-- source:
--   Cartis, Gould & Toint, On the complexity of steepest descent, Newton's and regularized Newton's methods, preprint 15 Oct 2009, p. 4, §2, after (2.15)

import Mathlib
import Definitions.Def_SlowConvergence_SteepestDescent_Data
import Definitions.Def_SlowConvergence_SteepestDescent_Hermite

namespace SlowConvergence.SteepestDescent

/-- Cartis, Gould & Toint, preprint 15 Oct 2009, §2, after (2.15), p. 4: the definition
`ψ_k = ((k+1)/(k+2))^{1/2+η}` implies `|ψ_k| ∈ (0, 1)` for all `k ≥ 0`. -/
theorem psi_mem (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) (k : ℕ) :
    0 < psi τ k ∧ psi τ k < 1 := by sorry

end SlowConvergence.SteepestDescent
