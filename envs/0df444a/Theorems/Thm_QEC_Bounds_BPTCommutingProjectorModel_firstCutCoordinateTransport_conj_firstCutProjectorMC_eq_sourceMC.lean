-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCutCoordinateTransport_conj_firstCutProjectorMC_eq_sourceMC
-- name    : QEC.Bounds.BPTCommutingProjectorModel.firstCutCoordinateTransport_conj_firstCutProjectorMC_eq_sourceMC
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T14:18:10.372834+00:00
-- url     : https://prove2.me/theorems/244b0b73-01ea-4fcc-800c-eea95c53e4af
-- title:
--   BPTCommuting Projector Model: first Cut Coordinate Transport conj first Cut Projector MC eq source MC
-- statement:
--   The transported first-cut `MC` projector is the transported source `Pi_AB Pi_BC`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2949-L2969
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2949-L2969

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

theorem QEC.Bounds.BPTCommutingProjectorModel.firstCutCoordinateTransport_conj_firstCutProjectorMC_eq_sourceMC
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.firstCutCoordinateTransport region).conjOperator
      (overlapLiftLeft (C := M.fourFactorD region) (M.firstCutProjectorMC region)) =
      (M.fourFactorTransport region).conjOperator
        (M.projectorAB region * M.projectorBC region) := by sorry
