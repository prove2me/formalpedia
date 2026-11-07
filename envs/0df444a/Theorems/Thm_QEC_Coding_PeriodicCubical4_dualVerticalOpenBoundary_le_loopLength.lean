-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_dualVerticalOpenBoundary_le_loopLength
-- name    : QEC.Coding.PeriodicCubical4.dualVerticalOpenBoundary_le_loopLength
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:44:54.404787+00:00
-- url     : https://prove2.me/theorems/a08f0de6-711f-48a2-93e5-264ce8ec5bdb
-- title:
--   Periodic Cubical4: dual Vertical Open Boundary le loop Length
-- statement:
--   The Periodic Cubical4 construction uses the dual Vertical Open Boundary le loop Length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L1176-L1186
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L1176-L1186

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.dualVerticalOpenBoundary_le_loopLength
    (m : Word (ZMod 2) (Plaquette L)) :
    HammingWeight (fun q : Fin L × Fin (L - 1) =>
      BinarySquare.verticalDerivative (dualSquareProjection m) q.1 q.2) ≤
      dualLoopLength m := by sorry
