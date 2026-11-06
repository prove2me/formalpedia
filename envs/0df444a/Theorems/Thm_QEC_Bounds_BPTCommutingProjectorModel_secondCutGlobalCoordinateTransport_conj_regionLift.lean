-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutGlobalCoordinateTransport_conj_regionLift
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCutGlobalCoordinateTransport_conj_regionLift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:35:25.053026+00:00
-- url     : https://prove2.me/theorems/7be4eb57-386e-47d9-8718-f113474e8aba
-- title:
--   BPTCommuting Projector Model: second Cut Global Coordinate Transport conj region Lift
-- statement:
--   The preceding physical-region locality equation in the literal second-cut
--   coordinates.  It is the exact route by which a probe of the eventual
--   `Pleft` factor is supplied to `RegionErasureRecoverable region`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/Transport.lean#L61-L103
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/Transport.lean#L61-L103

import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_RankOne
import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_Transport
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCutGlobalCoordinateTransport_conj_regionLift
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (P : Semantics.Operator (M.regionSubsystem region).selectedSystem) :
    (M.secondCutGlobalCoordinateTransport region).conjOperator
      ((M.regionSubsystem region).extendLocalToRegister P) =
      overlapLiftLeft
        (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
        (((M.regionSubsystem (M.interior region)).selectedFactorization
          (M.regionSubsystem region) (by
            intro site hsite
            exact (Finset.mem_sdiff.mp hsite).1)).conjOperator P) := by sorry
