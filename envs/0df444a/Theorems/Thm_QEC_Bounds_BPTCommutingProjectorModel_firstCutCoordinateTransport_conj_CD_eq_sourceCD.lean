-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCutCoordinateTransport_conj_CD_eq_sourceCD
-- name    : QEC.Bounds.BPTCommutingProjectorModel.firstCutCoordinateTransport_conj_CD_eq_sourceCD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:25:49.320079+00:00
-- url     : https://prove2.me/theorems/07b690eb-dff8-4f1c-98d9-8e0f27504dfd
-- title:
--   BPTCommuting Projector Model: first Cut Coordinate Transport conj CD eq source CD
-- statement:
--   The transported first-cut `CD` projector is the transported source `Pi_CD`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2972-L2988
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2972-L2988

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

theorem QEC.Bounds.BPTCommutingProjectorModel.firstCutCoordinateTransport_conj_CD_eq_sourceCD
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.firstCutCoordinateTransport region).conjOperator
      (overlapLiftRight
        (A := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
        (M.fourFactorProjectorCDLocal region)) =
      (M.fourFactorTransport region).conjOperator (M.projectorCD region) := by sorry
