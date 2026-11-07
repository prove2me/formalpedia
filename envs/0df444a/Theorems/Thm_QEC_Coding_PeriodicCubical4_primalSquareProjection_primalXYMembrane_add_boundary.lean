-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_primalSquareProjection_primalXYMembrane_add_boundary
-- name    : QEC.Coding.PeriodicCubical4.primalSquareProjection_primalXYMembrane_add_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:41:52.09559+00:00
-- url     : https://prove2.me/theorems/14b815be-2a5e-4286-9cdc-d6d8c08fe6b7
-- title:
--   Periodic Cubical4: primal Square Projection primal XYMembrane add boundary
-- statement:
--   Every representative of the primal membrane homology class has all-one
--   primal projection.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L593-L606
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L593-L606

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.primalSquareProjection_primalXYMembrane_add_boundary
    (z₀ w₀ : ZMod L) (c : Word (ZMod 2) (Cube L)) :
    primalSquareProjection (primalXYMembrane z₀ w₀ + boundary3 c) =
      fun _ _ => 1 := by sorry
