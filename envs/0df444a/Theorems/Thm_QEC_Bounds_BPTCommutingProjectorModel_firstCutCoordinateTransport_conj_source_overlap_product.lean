-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCutCoordinateTransport_conj_source_overlap_product
-- name    : QEC.Bounds.BPTCommutingProjectorModel.firstCutCoordinateTransport_conj_source_overlap_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:18:08.917613+00:00
-- url     : https://prove2.me/theorems/ed208108-450c-4f8e-9374-6c541b58911b
-- title:
--   BPTCommuting Projector Model: first Cut Coordinate Transport conj source overlap product
-- statement:
--   The first-cut overlap pair is exactly the full BPT code projector after its
--   explicit coordinate transport.  This is the source equation
--   `Pi = Pi_MC Pi_CD`, not a spectral replacement for it.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2914-L2946
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2914-L2946

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

theorem QEC.Bounds.BPTCommutingProjectorModel.firstCutCoordinateTransport_conj_source_overlap_product
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.firstCutCoordinateTransport region).conjOperator
      (overlapLiftLeft (C := M.fourFactorD region) (M.firstCutProjectorMC region) *
        overlapLiftRight
          (A := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
          (M.fourFactorProjectorCDLocal region)) =
      (M.fourFactorTransport region).conjOperator M.fullCodeProjector := by sorry
