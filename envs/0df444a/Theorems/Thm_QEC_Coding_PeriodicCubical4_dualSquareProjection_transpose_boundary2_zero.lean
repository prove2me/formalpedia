-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_dualSquareProjection_transpose_boundary2_zero
-- name    : QEC.Coding.PeriodicCubical4.dualSquareProjection_transpose_boundary2_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:29:45.773782+00:00
-- url     : https://prove2.me/theorems/f6a11ee2-6157-4c92-89bc-c5682d473ca7
-- title:
--   Periodic Cubical4: dual Square Projection transpose boundary2 zero
-- statement:
--   The Periodic Cubical4 construction uses the dual Square Projection transpose boundary2 zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L944-L952
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L944-L952

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000

theorem QEC.Coding.PeriodicCubical4.dualSquareProjection_transpose_boundary2_zero {L : Nat}
    [NeZero L] [Fact (1 < L)]
    (e : Word (ZMod 2) (Link L)) :
    dualSquareProjection (wordLinearMapTranspose boundary2 e) =
      (0 : BinarySquare.Grid L) := by sorry
