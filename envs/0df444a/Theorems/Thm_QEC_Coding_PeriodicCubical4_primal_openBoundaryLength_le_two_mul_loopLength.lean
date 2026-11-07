-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_primal_openBoundaryLength_le_two_mul_loopLength
-- name    : QEC.Coding.PeriodicCubical4.primal_openBoundaryLength_le_two_mul_loopLength
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:37:04.989885+00:00
-- url     : https://prove2.me/theorems/e37bfa60-dd2e-4791-bd80-bc1fbacbf8c2
-- title:
--   Periodic Cubical4: primal open Boundary Length le two mul loop Length
-- statement:
--   The open edge boundary of the primal square projection is controlled by
--   twice the actual primal syndrome-loop length.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L943-L952
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L943-L952

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.primal_openBoundaryLength_le_two_mul_loopLength
    (m : Word (ZMod 2) (Plaquette L)) :
    BinarySquare.openBoundaryLength (primalSquareProjection m) ≤
      2 * primalLoopLength m := by sorry
