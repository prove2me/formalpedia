-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_primalVerticalDerivative_eq_fiberPairing
-- name    : QEC.Coding.PeriodicCubical4.primalVerticalDerivative_eq_fiberPairing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:42:25.720661+00:00
-- url     : https://prove2.me/theorems/cc063223-14ac-442d-91df-04eac60dac8b
-- title:
--   Periodic Cubical4: primal Vertical Derivative eq fiber Pairing
-- statement:
--   A vertical projected edge is the parity of the primal defect loop on
--   the corresponding `x`-link fiber.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L821-L838
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L821-L838

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.primalVerticalDerivative_eq_fiberPairing
    (m : Word (ZMod 2) (Plaquette L)) (x : Fin L) (i : Fin (L - 1)) :
    BinarySquare.verticalDerivative (primalSquareProjection m) x i =
      wordPairing
        (primalVerticalLinkFiber
          (finToPeriodic x)
          (finToPeriodic (⟨i.1 + 1, by omega⟩ : Fin L)))
        (primalDefectLoop m) := by sorry
