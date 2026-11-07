-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_dual_openBoundaryLength_le_two_mul_loopLength
-- name    : QEC.Coding.PeriodicCubical4.dual_openBoundaryLength_le_two_mul_loopLength
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:37:36.570213+00:00
-- url     : https://prove2.me/theorems/93ec6979-ae8d-459c-96ee-99716afc92d6
-- title:
--   Periodic Cubical4: dual open Boundary Length le two mul loop Length
-- statement:
--   The open edge boundary of the dual square projection is controlled by
--   twice the actual dual syndrome-loop length.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L1190-L1199
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L1190-L1199

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.dual_openBoundaryLength_le_two_mul_loopLength
    (m : Word (ZMod 2) (Plaquette L)) :
    BinarySquare.openBoundaryLength (dualSquareProjection m) ≤
      2 * dualLoopLength m := by sorry
