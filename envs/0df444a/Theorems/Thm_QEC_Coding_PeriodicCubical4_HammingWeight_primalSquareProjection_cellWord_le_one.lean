-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_HammingWeight_primalSquareProjection_cellWord_le_one
-- name    : QEC.Coding.PeriodicCubical4.HammingWeight_primalSquareProjection_cellWord_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:38:37.413211+00:00
-- url     : https://prove2.me/theorems/94ee35cc-1e60-4236-9446-50212004f497
-- title:
--   Periodic Cubical4: Hamming Weight primal Square Projection cell Word le one
-- statement:
--   A single plaquette changes at most one primal projected square cell.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L453-L460
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L453-L460

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.HammingWeight_primalSquareProjection_cellWord_le_one (p : Plaquette L) :
    HammingWeight
        ((fun q : Fin L × Fin L =>
          primalSquareProjection (L := L) (cellWord p) q.1 q.2) :
          Word (ZMod 2) (Fin L × Fin L)) ≤ 1 := by sorry
