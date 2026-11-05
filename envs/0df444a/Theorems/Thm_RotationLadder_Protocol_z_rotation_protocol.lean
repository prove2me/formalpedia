-- Prove2me | Theorems.Thm_RotationLadder_Protocol_z_rotation_protocol
-- name    : RotationLadder.Protocol.z_rotation_protocol
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:40:09.624623+00:00
-- url     : https://prove2.me/theorems/9884741b-5dea-4cd2-8733-ddfb4b9be34b
-- title:
--   The closest-level protocol reaches every $Z$-rotation to every accuracy
-- statement:
--   Let $\mathrm{pick}$ be a closest-level rule, $\varphi$ a real target and $\varepsilon>0$. With fair independent measurement outcomes:
--
--   1. almost surely the run stops, and the rotation $Z(\varphi-r_\tau)$ it has applied has accuracy at most $\varepsilon$ against $Z(\varphi)$;
--   2. the expected online cost $\mathbb E[\tau]$ is finite;
--   3. the expected offline cost is finite.
--
--   The paper supports this claim by simulation.
--
--   Differences from the source:
--   - reading: step 3 says 2θ_i is close to φ; p. 3 says closest → a closest level, for every tie-break; reason: p. 3 fixes the meaning; covering every tie-break leaves no case out
--   - reading: the p. 4 step list treats all levels alike; p. 3 says a failed T gate is always corrected deterministically by S → level 0 moves the residual by sign(r)·π/4 whatever the outcome, with S or S† applied when needed; reason: the paper calls this a crucial fact (p. 3); without it a failure at level 0 would not be corrected
--   - reading: we can actually apply any Z-rotation rapidly and with good accuracy (p. 3), supported by simulation → almost sure stopping at accuracy ε, with finite expected online and offline cost, for every ε > 0; reason: the source gives no quantified statement of rapidly; its only quantified form is a fit on 10⁻¹² < ϵ < 10⁻⁴, which is not a claim about all ϵ
--   - generalization: the simulation takes 0 < φ < 2π → every real target φ; reason: specializes to the simulated range
--   - encoding: one simulated ladder per step, averaged → each step's ladder enters through its mean cost; reason: the ladder randomness is independent of the outcomes, so the expectations agree
-- source:
--   Duclos-Cianci, Svore, A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations, arXiv:1210.1980v1, Sec. III, unnumbered, pp. 3-4

import Mathlib
import Definitions.Def_RotationLadder_Protocol_IsClosestRule
import Definitions.Def_RotationLadder_Protocol_applied
import Definitions.Def_RotationLadder_Protocol_coinLaw
import Definitions.Def_RotationLadder_Protocol_offlineCost
open scoped ENNReal

namespace RotationLadder.Protocol

/-- **Every `Z`-rotation is reached to every accuracy.**
Duclos-Cianci, Svore, *A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations*,
arXiv:1210.1980v1, Sec. III, unnumbered, pp. 3-4.

For every closest rule, every real target `φ` and every `ε > 0`: almost surely the run stops, and
the rotation it has applied has accuracy at most `ε`; the expected online and offline costs are
finite.

**Formalization Note.** The paper simulates `0 < φ < 2π`, and supports the claim by simulation. -/
theorem z_rotation_protocol (pick : ℝ → ℕ) (hpick : IsClosestRule pick) (φ ε : ℝ) (hε : 0 < ε) :
    (∀ᵐ ω ∂coinLaw, stopTime pick φ ε ω < ⊤ ∧
      accuracy (zRot φ) (zRot (applied pick φ ε ω)) ≤ ε) ∧
    (∫⁻ ω, ((stopTime pick φ ε ω : ℕ∞) : ℝ≥0∞) ∂coinLaw < ⊤) ∧
    (∫⁻ ω, offlineCost pick φ ε ω ∂coinLaw < ⊤) := by sorry

end RotationLadder.Protocol
