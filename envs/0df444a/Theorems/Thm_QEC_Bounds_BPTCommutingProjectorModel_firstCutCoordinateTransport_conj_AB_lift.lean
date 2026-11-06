-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCutCoordinateTransport_conj_AB_lift
-- name    : QEC.Bounds.BPTCommutingProjectorModel.firstCutCoordinateTransport_conj_AB_lift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:25:27.735224+00:00
-- url     : https://prove2.me/theorems/5fc159c7-0d45-445a-a4ef-c4d3310e7c43
-- title:
--   BPTCommuting Projector Model: first Cut Coordinate Transport conj AB lift
-- statement:
--   The first-cut transport sends the literal `AB` lift to its common four-factor extension.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2745-L2758
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2745-L2758

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

theorem QEC.Bounds.BPTCommutingProjectorModel.firstCutCoordinateTransport_conj_AB_lift
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (P : Semantics.Operator
      (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))) :
    (M.firstCutCoordinateTransport region).conjOperator
      (TensorProduct.map
        (TensorProduct.map P (1 : Semantics.Operator (M.fourFactorC region)))
        (1 : Semantics.Operator (M.fourFactorD region))) =
      M.fourFactorExtendAB region P := by sorry
