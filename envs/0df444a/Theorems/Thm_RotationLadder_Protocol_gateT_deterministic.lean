-- Prove2me | Theorems.Thm_RotationLadder_Protocol_gateT_deterministic
-- name    : RotationLadder.Protocol.gateT_deterministic
-- status  : Proved
-- author  : @iris
-- created : 2026-11-04T06:34:46.728081+00:00
-- url     : https://prove2.me/theorems/44bae49d-0c8f-4271-b7c0-c64dccd220bd
-- title:
--   The correction $ST^\dagger=T$
-- statement:
--   With $T=Z(\pi/4)$, $T^\dagger=Z(-\pi/4)$ and $S=Z(\pi/2)$,
--
--   $$S\,T^\dagger=T .$$
--
--   So when the circuit of Fig. 1 applies $T^\dagger$ instead of $T$, the Clifford gate $S$ repairs the error deterministically. This makes level 0 of the ladder a deterministic step of the protocol.
--
--   Differences from the source: none.
-- source:
--   Duclos-Cianci, Svore, A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations, arXiv:1210.1980v1, Sec. I, unnumbered, p. 2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_RotationLadder_Protocol_zRot

namespace RotationLadder.Protocol

/-- **The correction `S T† = T`.**
Duclos-Cianci, Svore, *A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations*,
arXiv:1210.1980v1, Sec. I, unnumbered, p. 2.

**Formalization Note.** `T = gateT = zRot (π/4)`, `T† = zRot (-π/4)` and `S = phaseS = zRot (π/2)`.
-/
theorem gateT_deterministic :
    QAlgorithms.phaseS * zRot (-(Real.pi / 4)) = QAlgorithms.gateT ∧
      zRot (Real.pi / 4) = QAlgorithms.gateT ∧ zRot (Real.pi / 2) = QAlgorithms.phaseS := by sorry

end RotationLadder.Protocol
