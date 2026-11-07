-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_primalFullRowCount_dist_succ_le_one
-- name    : QEC.Coding.PeriodicCubical4.primalFullRowCount_dist_succ_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:37:15.432329+00:00
-- url     : https://prove2.me/theorems/2905e2c0-fd9c-4819-8fee-1dadd9c32c3c
-- title:
--   Periodic Cubical4: primal Full Row Count dist succ le one
-- statement:
--   The Periodic Cubical4 construction uses the primal Full Row Count dist succ le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L1419-L1425
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L1419-L1425

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.primalFullRowCount_dist_succ_le_one
    (γ : PauliErrorPath (ι := Plaquette L)) (n : Nat)
    (hn : n < γ.increments.length) :
    Nat.dist (primalFullRowCount γ (n + 1))
      (primalFullRowCount γ n) ≤ 1 := by sorry
