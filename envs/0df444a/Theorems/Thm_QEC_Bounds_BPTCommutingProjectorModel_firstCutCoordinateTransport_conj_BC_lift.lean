-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCutCoordinateTransport_conj_BC_lift
-- name    : QEC.Bounds.BPTCommutingProjectorModel.firstCutCoordinateTransport_conj_BC_lift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:25:54.0192+00:00
-- url     : https://prove2.me/theorems/ba1d0da6-932c-4006-b477-658d4485d6aa
-- title:
--   BPTCommuting Projector Model: first Cut Coordinate Transport conj BC lift
-- statement:
--   The first-cut transport sends the literal `BC` lift to its common four-factor extension.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2785-L2825
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2785-L2825

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

theorem QEC.Bounds.BPTCommutingProjectorModel.firstCutCoordinateTransport_conj_BC_lift
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (P : Semantics.Operator
      (Semantics.CompositeSystem (M.fourFactorB region) (M.fourFactorC region))) :
    (M.firstCutCoordinateTransport region).conjOperator
      (TensorProduct.map
        (overlapLiftRight (A := M.fourFactorA region) P)
        (1 : Semantics.Operator (M.fourFactorD region))) =
      M.fourFactorExtendBC region P := by sorry
