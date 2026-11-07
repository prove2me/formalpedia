-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_primalSquareProjection_cellWord_apply
-- name    : QEC.Coding.PeriodicCubical4.primalSquareProjection_cellWord_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:27:10.196546+00:00
-- url     : https://prove2.me/theorems/9d8f99ff-9328-4fbf-bfbc-d8a4b6994b79
-- title:
--   Periodic Cubical4: primal Square Projection cell Word apply
-- statement:
--   The Periodic Cubical4 construction uses the primal Square Projection cell Word apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L407-L418
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L407-L418

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.primalSquareProjection_cellWord_apply (p : Plaquette L)
    (y x : Fin L) :
    primalSquareProjection (cellWord p) y x =
      if p.2 = .xy ∧ finToPeriodic x = p.1 .x ∧
          finToPeriodic y = p.1 .y then 1 else 0 := by sorry
