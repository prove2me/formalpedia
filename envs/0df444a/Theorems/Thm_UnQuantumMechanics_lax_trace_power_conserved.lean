-- Prove2me | Theorems.Thm_UnQuantumMechanics_lax_trace_power_conserved
-- name    : UnQuantumMechanics.lax_trace_power_conserved
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T14:45:53.741508+00:00
-- url     : https://prove2.me/theorems/539c17ed-3824-4d5e-9811-f7ca56eec4af
-- title:
--   Lax pair: $\operatorname{Tr}(S^k)$ is a constant of motion
-- statement:
--   Let $\tau\mapsto H(\tau)$ and $\tau\mapsto S(\tau)$ be real $m\times m$ matrix-valued functions such that $S$ is differentiable at every time and obeys the Lax equation
--   $$\dot S(\tau) = H(\tau)S(\tau) - S(\tau)H(\tau)\qquad\text{for all } \tau .$$
--   Then for every $k\in\mathbb N$ the trace of $S^k$ is a constant of motion:
--   $$\operatorname{Tr}\big(S(\tau)^k\big) = \operatorname{Tr}\big(S(0)^k\big)\qquad\text{for all }\tau .$$
--
--   **Formalization Note** $H$ is allowed to depend on time (the paper remarks the statement holds beyond the linear case); derivatives are entrywise; $m$ is an arbitrary finite index set, and $k = 0$ is included.
-- source:
--   C. Baumgarten, How to (Un-) Quantum Mechanics, arXiv:1810.06981v2 [physics.gen-ph] (v2 dated June 10, 2025), https://arxiv.org/abs/1810.06981, Sec. VI, p. 16–17, Eq. (47)

import Mathlib
import Definitions.Def_UnQM_phase_space

open Matrix

namespace UnQuantumMechanics

theorem lax_trace_power_conserved {m : Type} [Fintype m] [DecidableEq m]
    (H S : ℝ → Matrix m m ℝ)
    (hS : ∀ τ i j, HasDerivAt (fun t => S t i j) ((H τ * S τ - S τ * H τ) i j) τ)
    (k : ℕ) (τ : ℝ) :
    (S τ ^ k).trace = (S 0 ^ k).trace := by sorry

end UnQuantumMechanics
