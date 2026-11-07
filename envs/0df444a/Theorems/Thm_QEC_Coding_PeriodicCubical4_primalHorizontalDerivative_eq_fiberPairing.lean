-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_primalHorizontalDerivative_eq_fiberPairing
-- name    : QEC.Coding.PeriodicCubical4.primalHorizontalDerivative_eq_fiberPairing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:41:53.70108+00:00
-- url     : https://prove2.me/theorems/d832033d-fd70-4c19-be7a-101bc0e66d3e
-- title:
--   Periodic Cubical4: primal Horizontal Derivative eq fiber Pairing
-- statement:
--   A horizontal projected edge is the parity of the primal defect loop on
--   the corresponding `y`-link fiber.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L800-L817
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L800-L817

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.primalHorizontalDerivative_eq_fiberPairing
    (m : Word (ZMod 2) (Plaquette L)) (y : Fin L) (i : Fin (L - 1)) :
    BinarySquare.horizontalDerivative (primalSquareProjection m) y i =
      wordPairing
        (primalHorizontalLinkFiber
          (finToPeriodic (⟨i.1 + 1, by omega⟩ : Fin L))
          (finToPeriodic y))
        (primalDefectLoop m) := by sorry
