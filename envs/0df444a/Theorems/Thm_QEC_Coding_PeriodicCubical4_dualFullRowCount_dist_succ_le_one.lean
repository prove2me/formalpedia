-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_dualFullRowCount_dist_succ_le_one
-- name    : QEC.Coding.PeriodicCubical4.dualFullRowCount_dist_succ_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:37:39.299862+00:00
-- url     : https://prove2.me/theorems/c621943c-98cf-4bd5-b1c4-3fd539aa4e51
-- title:
--   Periodic Cubical4: dual Full Row Count dist succ le one
-- statement:
--   The Periodic Cubical4 construction uses the dual Full Row Count dist succ le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L1427-L1433
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L1427-L1433

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.dualFullRowCount_dist_succ_le_one
    (γ : PauliErrorPath (ι := Plaquette L)) (n : Nat)
    (hn : n < γ.increments.length) :
    Nat.dist (dualFullRowCount γ (n + 1))
      (dualFullRowCount γ n) ≤ 1 := by sorry
