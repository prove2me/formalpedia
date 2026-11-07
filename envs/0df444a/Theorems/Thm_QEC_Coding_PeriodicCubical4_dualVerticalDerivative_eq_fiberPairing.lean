-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_dualVerticalDerivative_eq_fiberPairing
-- name    : QEC.Coding.PeriodicCubical4.dualVerticalDerivative_eq_fiberPairing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:45:28.78085+00:00
-- url     : https://prove2.me/theorems/4c44537a-c6c2-4980-afdf-6b1d2f682448
-- title:
--   Periodic Cubical4: dual Vertical Derivative eq fiber Pairing
-- statement:
--   A vertical dual projected edge is the parity of the dual defect loop on
--   the corresponding `xyw` cube fiber.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L1083-L1096
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L1083-L1096

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.dualVerticalDerivative_eq_fiberPairing
    (m : Word (ZMod 2) (Plaquette L)) (z : Fin L) (i : Fin (L - 1)) :
    BinarySquare.verticalDerivative (dualSquareProjection m) z i =
      wordPairing
        (dualVerticalCubeFiber
          (finToPeriodic z)
          (finToPeriodic (⟨i.1, by omega⟩ : Fin L)))
        (dualDefectLoop m) := by sorry
