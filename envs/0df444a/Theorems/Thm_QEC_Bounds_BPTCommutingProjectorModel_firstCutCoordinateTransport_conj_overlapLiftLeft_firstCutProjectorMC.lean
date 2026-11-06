-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCutCoordinateTransport_conj_overlapLiftLeft_firstCutProjectorMC
-- name    : QEC.Bounds.BPTCommutingProjectorModel.firstCutCoordinateTransport_conj_overlapLiftLeft_firstCutProjectorMC
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:20:33.779541+00:00
-- url     : https://prove2.me/theorems/cd5dab74-58f3-4f1a-8079-d4f6afa26cce
-- title:
--   BPTCommuting Projector Model: first Cut Coordinate Transport conj overlap Lift Left first Cut Projector MC
-- statement:
--   The first source product has the literal first-cut overlap form.  This is the
--   `Pi_MC` support equation used to instantiate the BV03 block theorem; it is
--   derived from the independent `AB` and `BC` source-local representatives.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2832-L2885
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2832-L2885

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

theorem QEC.Bounds.BPTCommutingProjectorModel.firstCutCoordinateTransport_conj_overlapLiftLeft_firstCutProjectorMC
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.firstCutCoordinateTransport region).conjOperator
      (overlapLiftLeft (C := M.fourFactorD region) (M.firstCutProjectorMC region)) =
      M.fourFactorExtendAB region (M.fourFactorProjectorABLocal region) *
        M.fourFactorExtendBC region (M.fourFactorProjectorBCLocal region) := by sorry
