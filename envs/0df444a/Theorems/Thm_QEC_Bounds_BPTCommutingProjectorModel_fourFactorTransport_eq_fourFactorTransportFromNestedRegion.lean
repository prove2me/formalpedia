-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorTransport_eq_fourFactorTransportFromNestedRegion
-- name    : QEC.Bounds.BPTCommutingProjectorModel.fourFactorTransport_eq_fourFactorTransportFromNestedRegion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:20:40.937206+00:00
-- url     : https://prove2.me/theorems/6238cdb3-3736-415b-826c-6d190ef94aef
-- title:
--   BPTCommuting Projector Model: four Factor Transport eq four Factor Transport From Nested Region
-- statement:
--   The right-nested and original cumulative `A,B,C,D` factorizations coincide.
--   The proof is a basis calculation using the already-proved coherence of the
--   two nested coordinate splits.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L3447-L3487
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L3447-L3487

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 800000

theorem QEC.Bounds.BPTCommutingProjectorModel.fourFactorTransport_eq_fourFactorTransportFromNestedRegion
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    M.fourFactorTransport region = M.fourFactorTransportFromNestedRegion region := by sorry
