-- Prove2me | Theorems.Thm_RotationLadder_Protocol_euler_xzx
-- name    : RotationLadder.Protocol.euler_xzx
-- status  : Proved
-- author  : @iris
-- created : 2026-11-04T06:35:40.970115+00:00
-- url     : https://prove2.me/theorems/a74d54a0-9527-44b1-b907-c10a77410b71
-- title:
--   $U\propto X(\alpha)Z(\beta)X(\gamma)$
-- statement:
--   Every single-qubit unitary $U$ can be written
--
--   $$U=e^{i\kappa}\,X(\alpha)\,Z(\beta)\,X(\gamma)$$
--
--   for some real $\alpha,\beta,\gamma,\kappa$. So three rotations about the $X$- and $Z$-axes give any single-qubit gate up to a global phase.
--
--   Differences from the source:
--   - encoding: an analogous circuit performs a rotation about the X-axis → X(α) := H Z(α) H; reason: conjugation by the Clifford H exchanges the two axes
--   - encoding: U ∝ X(α)Z(β)X(γ) → U = e^{iκ} X(α)Z(β)X(γ); reason: a proportionality constant between unitaries is a phase
-- source:
--   Duclos-Cianci, Svore, A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations, arXiv:1210.1980v1, Sec. III, unnumbered, p. 5

import Mathlib
import Definitions.Def_RotationLadder_Protocol_xRot

namespace RotationLadder.Protocol

/-- **Three rotations give every single-qubit unitary.**
Duclos-Cianci, Svore, *A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations*,
arXiv:1210.1980v1, Sec. III, unnumbered, p. 5: `U ∝ X(α)Z(β)X(γ)`. -/
theorem euler_xzx :
    ∀ U ∈ Matrix.unitaryGroup Bool ℂ, ∃ α β γ κ : ℝ,
      U = Complex.exp (Complex.I * (κ : ℂ)) • (xRot α * zRot β * xRot γ) := by sorry

end RotationLadder.Protocol
