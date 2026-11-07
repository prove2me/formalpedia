-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_dualSquareProjection_cellWord_apply
-- name    : QEC.Coding.PeriodicCubical4.dualSquareProjection_cellWord_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:26:50.503218+00:00
-- url     : https://prove2.me/theorems/ca6b52d5-b7b0-4492-bb8b-2c0122d7515b
-- title:
--   Periodic Cubical4: dual Square Projection cell Word apply
-- statement:
--   The Periodic Cubical4 construction uses the dual Square Projection cell Word apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L420-L430
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L420-L430

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.dualSquareProjection_cellWord_apply (p : Plaquette L)
    (w z : Fin L) :
    dualSquareProjection (cellWord p) w z =
      if p.2 = .xy ∧ p.1 .z = finToPeriodic z ∧
          p.1 .w = finToPeriodic w then 1 else 0 := by sorry
