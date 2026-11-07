-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_primalSquareProjection_add
-- name    : QEC.Coding.PeriodicCubical4.primalSquareProjection_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:35:23.465049+00:00
-- url     : https://prove2.me/theorems/4611a90b-f602-4e89-99eb-4f727b704606
-- title:
--   Periodic Cubical4: primal Square Projection add
-- statement:
--   The Periodic Cubical4 construction uses the primal Square Projection add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L575-L581
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L575-L581

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.primalSquareProjection_add
    (m₁ m₂ : Word (ZMod 2) (Plaquette L)) :
    primalSquareProjection (m₁ + m₂) =
      primalSquareProjection m₁ + primalSquareProjection m₂ := by sorry
