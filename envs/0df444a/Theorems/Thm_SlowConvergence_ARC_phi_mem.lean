-- Prove2me | Theorems.Thm_SlowConvergence_ARC_phi_mem
-- name    : SlowConvergence.ARC.phi_mem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:44:00.527984+00:00
-- url     : https://prove2.me/theorems/66c793fb-4445-41f6-9b33-a2f6647ea230
-- title:
--   §5, p. 14 — $\phi_k\in(0,1)$ for all $k\ge0$
-- statement:
--   Let $0<\tau<1$, $\eta = \tfrac12\big(\tfrac2{3-2\tau}-\tfrac23\big)$, $\mu = \tfrac23+2\eta$ and
--   $$\phi_k = (k+1)^\mu\Big[\Big(\frac1{k+1}\Big)^\mu - \Big(\frac1{k+2}\Big)^\mu\Big].$$
--   Then $0 < \phi_k < 1$ for every $k\ge0$.
--
--   This bounds the coefficients (5.11) of the Hermite pieces uniformly in $k$.
-- source:
--   Cartis, Gould & Toint, On the complexity of steepest descent, Newton's and regularized Newton's methods, preprint 15 Oct 2009, p. 14, §5, after (5.11)

import Mathlib
import Definitions.Def_SlowConvergence_ARC_Data
import Definitions.Def_SlowConvergence_ARC_Pieces

namespace SlowConvergence.ARC

/-- Cartis, Gould & Toint, preprint 15 Oct 2009, §5, p. 14: "The definition of φ_k implies that
φ_k ∈ (0, 1) for all k ≥ 0", where `φ_k = (k+1)^µ[(1/(k+1))^µ − (1/(k+2))^µ]` and `µ = 2/3 + 2η`. -/
theorem phi_mem (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) (k : ℕ) :
    0 < phi τ k ∧ phi τ k < 1 := by sorry

end SlowConvergence.ARC
