-- Prove2me | Theorems.Thm_RotationLadder_Protocol_ladder_bounds
-- name    : RotationLadder.Protocol.ladder_bounds
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:35:41.292137+00:00
-- url     : https://prove2.me/theorems/942563f9-4883-4db5-afaf-0592df849ee0
-- title:
--   $\tfrac34\le p_{0,i}<\cos^2\frac{\pi}{8}$ and $0<\theta_i<\frac{\pi}{4}$
-- statement:
--   For every level $i\ge0$,
--
--   $$\frac34\le p_{0,i}<\cos^2\frac{\pi}{8}=0.853\ldots,\qquad\qquad 0<\theta_i<\frac{\pi}{4}.$$
--
--   The walk on the ladder is therefore biased upward at every level, which is what makes each level cheap to reach.
--
--   Differences from the source:
--   - reading: 0 < θ_i < π/4 (∀i) → every level i ≥ 0; reason: at i = −1, θ = π/4 and p = 1/2, so the paper's ∀i can only range over the levels of the ladder
--   - encoding: cos²(π/8) = 0.853 . . . → 0.853 < cos²(π/8) < 0.854; reason: a truncated decimal says exactly this
-- source:
--   Duclos-Cianci, Svore, A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations, arXiv:1210.1980v1, Sec. II, unnumbered, p. 3

import Mathlib
import Definitions.Def_RotationLadder_Protocol_ladderProb

namespace RotationLadder.Protocol

/-- **The bounds on the ladder.**
Duclos-Cianci, Svore, *A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations*,
arXiv:1210.1980v1, Sec. II, unnumbered, p. 3.

`3/4 ≤ p_(0,i) < cos²(π/8) = 0.853…` and `0 < θ_i < π/4` for every level `i ≥ 0`.

**Formalization Note.** Levels are natural numbers. At `i = -1`, `θ = π/4`, outside the printed
range; the paper's `∀i` ranges over the ladder's levels. -/
theorem ladder_bounds :
    (∀ i : ℕ, 3 / 4 ≤ ladderProb i ∧ ladderProb i < Real.cos (Real.pi / 8) ^ 2 ∧
      0 < theta i ∧ theta i < Real.pi / 4) ∧
    0.853 < Real.cos (Real.pi / 8) ^ 2 ∧ Real.cos (Real.pi / 8) ^ 2 < 0.854 := by sorry

end RotationLadder.Protocol
