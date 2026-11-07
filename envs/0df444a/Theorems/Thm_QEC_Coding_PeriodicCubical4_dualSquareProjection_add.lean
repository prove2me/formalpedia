-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_dualSquareProjection_add
-- name    : QEC.Coding.PeriodicCubical4.dualSquareProjection_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:36:58.637171+00:00
-- url     : https://prove2.me/theorems/f5bafcd3-4160-47a2-8cd8-33c092128a10
-- title:
--   Periodic Cubical4: dual Square Projection add
-- statement:
--   The Periodic Cubical4 construction uses the dual Square Projection add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L583-L589
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L583-L589

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.dualSquareProjection_add
    (m₁ m₂ : Word (ZMod 2) (Plaquette L)) :
    dualSquareProjection (m₁ + m₂) =
      dualSquareProjection m₁ + dualSquareProjection m₂ := by sorry
