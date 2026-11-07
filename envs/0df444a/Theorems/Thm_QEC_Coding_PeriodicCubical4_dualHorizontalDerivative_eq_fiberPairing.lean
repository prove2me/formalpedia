-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_dualHorizontalDerivative_eq_fiberPairing
-- name    : QEC.Coding.PeriodicCubical4.dualHorizontalDerivative_eq_fiberPairing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:44:29.236051+00:00
-- url     : https://prove2.me/theorems/71196eea-1d51-4e6f-b83a-136df0b69bc2
-- title:
--   Periodic Cubical4: dual Horizontal Derivative eq fiber Pairing
-- statement:
--   A horizontal dual projected edge is the parity of the dual defect loop on
--   the corresponding `xyz` cube fiber.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L1066-L1079
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L1066-L1079

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.dualHorizontalDerivative_eq_fiberPairing
    (m : Word (ZMod 2) (Plaquette L)) (w : Fin L) (i : Fin (L - 1)) :
    BinarySquare.horizontalDerivative (dualSquareProjection m) w i =
      wordPairing
        (dualHorizontalCubeFiber
          (finToPeriodic (⟨i.1, by omega⟩ : Fin L))
          (finToPeriodic w))
        (dualDefectLoop m) := by sorry
