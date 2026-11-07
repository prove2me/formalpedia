-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_dualSquareProjection_dualXYMembrane_add_coboundary
-- name    : QEC.Coding.PeriodicCubical4.dualSquareProjection_dualXYMembrane_add_coboundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:44:35.722496+00:00
-- url     : https://prove2.me/theorems/e6dd2143-b24a-4fcf-b8b0-d5235f942042
-- title:
--   Periodic Cubical4: dual Square Projection dual XYMembrane add coboundary
-- statement:
--   Every representative of the dual membrane cohomology class has all-one
--   dual projection.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L610-L624
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L610-L624

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.dualSquareProjection_dualXYMembrane_add_coboundary
    (x₀ y₀ : ZMod L) (e : Word (ZMod 2) (Link L)) :
    dualSquareProjection
        (dualXYMembrane x₀ y₀ + wordLinearMapTranspose boundary2 e) =
      fun _ _ => 1 := by sorry
