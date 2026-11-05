-- Prove2me | Theorems.Thm_RotationLadder_Protocol_rotation_circuit
-- name    : RotationLadder.Protocol.rotation_circuit
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:34:51.851143+00:00
-- url     : https://prove2.me/theorems/6294a06f-750a-4011-9b8c-f9d9aa66c93c
-- title:
--   Fig. 1 applies $Z(\alpha)$ or $Z(-\alpha)$, each with amplitude $1/\sqrt2$
-- statement:
--   Let $\alpha$ be real and let $|\psi\rangle$ be a single-qubit vector. Apply $\Lambda(X)$ to $|Z(\alpha)\rangle|\psi\rangle$, with the second wire as control, and measure the first wire. Then the unnormalized state of the second wire is
--
--   $$\text{outcome }0:\ \ \frac{1}{\sqrt2}\,Z(\alpha)|\psi\rangle,\qquad\qquad\text{outcome }1:\ \ \frac{e^{i\alpha}}{\sqrt2}\,Z(-\alpha)|\psi\rangle .$$
--
--   So each outcome has probability $1/2$ for a unit $|\psi\rangle$, and the circuit applies the rotation by $\alpha$ or by $-\alpha$ at random, up to a global phase. This is the only way the protocol uses its non-Clifford resources.
--
--   Differences from the source:
--   - encoding: |Z(θ)⟩ written without 1/√2 and post-measurement states written up to normalization → normalized ketZ, unnormalized post-measurement vectors with explicit amplitudes; reason: fixes the constants; the squared norms are the paper's probabilities
-- source:
--   Duclos-Cianci, Svore, A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations, arXiv:1210.1980v1, Sec. I, unnumbered, p. 2, Fig. 1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_RotationLadder_Protocol_cnotSecond
import Definitions.Def_RotationLadder_Protocol_ketZ
import Definitions.Def_RotationLadder_Protocol_postOut
import Definitions.Def_RotationLadder_Protocol_zRot

namespace RotationLadder.Protocol

/-- **Fig. 1 applies `Z(α)` or `Z(-α)`.**
Duclos-Cianci, Svore, *A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations*,
arXiv:1210.1980v1, Sec. I, unnumbered, p. 2.

With `|Z(α)⟩` on the first wire and `ψ` on the second, outcome `0` leaves `(1/√2) Z(α)ψ` and outcome
`1` leaves `(1/√2) e^(iα) Z(-α)ψ`.

**Formalization Note.** The amplitude `1/√2` is the normalization of `ketZ`; both outcomes have
probability `1/2` for a unit `ψ`, and the phase `e^(iα)` is the paper's global phase. -/
theorem rotation_circuit :
    ∀ (α : ℝ) (ψ : EuclideanSpace ℂ Bool),
      postOut false (QAlgorithms.act cnotSecond (QAlgorithms.tensorVec (ketZ α) ψ)) =
          ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • QAlgorithms.act (zRot α) ψ ∧
      postOut true (QAlgorithms.act cnotSecond (QAlgorithms.tensorVec (ketZ α) ψ)) =
          (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * Complex.exp (Complex.I * (α : ℂ))) • QAlgorithms.act (zRot (-α)) ψ := by sorry

end RotationLadder.Protocol
