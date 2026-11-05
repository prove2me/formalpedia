-- Prove2me | Theorems.Thm_RotationLadder_Protocol_accuracy_same_axis
-- name    : RotationLadder.Protocol.accuracy_same_axis
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:35:12.563341+00:00
-- url     : https://prove2.me/theorems/579783a4-9a34-43aa-82d7-898ae44ab61f
-- title:
--   Accuracy of two rotations about the same axis is $|\sin((\varphi-\varphi')/2)|$
-- statement:
--   For all real $\varphi,\varphi'$, the accuracy of $Z(\varphi')$ against $Z(\varphi)$ is
--
--   $$\max_{|\psi\rangle}D\bigl(Z(\varphi)|\psi\rangle\langle\psi|Z(\varphi)^\dagger,\ Z(\varphi')|\psi\rangle\langle\psi|Z(\varphi')^\dagger\bigr)=\Bigl|\sin\frac{\varphi-\varphi'}{2}\Bigr| .$$
--
--   This turns the accuracy of a run into a condition on its remaining angle.
--
--   Differences from the source:
--   - reading: this reduces to the difference of rotation angles, ϵ = ∆φ, for small angles → the exact value |sin((φ − φ′)/2)|, for all angles; reason: with the paper's Z(θ) = diag(1, e^{iθ}) the small-angle value is |φ − φ′|/2, so ϵ = ∆φ holds only with ∆φ the half-angle, which is also what the paper's √(1 − |cos ∆φ|) needs
-- source:
--   Duclos-Cianci, Svore, A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations, arXiv:1210.1980v1, Sec. III, unnumbered, p. 4

import Mathlib
import Definitions.Def_RotationLadder_Protocol_accuracy
import Definitions.Def_RotationLadder_Protocol_zRot

namespace RotationLadder.Protocol

/-- **The accuracy of two rotations about the same axis.**
Duclos-Cianci, Svore, *A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations*,
arXiv:1210.1980v1, Sec. III, unnumbered, p. 4.

The accuracy of `Z(φ')` against `Z(φ)` is exactly `|sin((φ - φ')/2)|`.

**Formalization Note.** The paper's remark "this reduces to the difference of rotation angles,
`ϵ = ∆φ`" reads `∆φ` as the half-angle difference, in the small-angle limit. The formula stated
here is the exact value for the paper's `Z(θ) = diag(1, e^(iθ))`. -/
theorem accuracy_same_axis (φ φ' : ℝ) :
    accuracy (zRot φ) (zRot φ') = |Real.sin ((φ - φ') / 2)| := by sorry

end RotationLadder.Protocol
