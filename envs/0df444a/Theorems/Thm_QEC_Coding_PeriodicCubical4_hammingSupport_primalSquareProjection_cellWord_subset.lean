-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_hammingSupport_primalSquareProjection_cellWord_subset
-- name    : QEC.Coding.PeriodicCubical4.hammingSupport_primalSquareProjection_cellWord_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:40:07.777504+00:00
-- url     : https://prove2.me/theorems/99ad6d44-60fa-4fac-ab92-a7ea64848ec1
-- title:
--   Periodic Cubical4: hamming Support primal Square Projection cell Word subset
-- statement:
--   A single plaquette has primal projection supported at at most its one
--   ordered `xy` coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L434-L450
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L434-L450

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.hammingSupport_primalSquareProjection_cellWord_subset (p : Plaquette L) :
    hammingSupport
        ((fun q : Fin L × Fin L =>
          primalSquareProjection (L := L) (cellWord p) q.1 q.2) :
          Word (ZMod 2) (Fin L × Fin L)) ⊆
      {(periodicToFin (p.1 .y), periodicToFin (p.1 .x))} := by sorry
