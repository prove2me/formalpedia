-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCutCoordinateTransport_conj_overlapLiftRight_CD_lift
-- name    : QEC.Bounds.BPTCommutingProjectorModel.firstCutCoordinateTransport_conj_overlapLiftRight_CD_lift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:20:25.556371+00:00
-- url     : https://prove2.me/theorems/17ee7b30-dc71-43b9-ada3-411f3612bbc4
-- title:
--   BPTCommuting Projector Model: first Cut Coordinate Transport conj overlap Lift Right CD lift
-- statement:
--   The first-cut transport sends the literal `CD` overlap lift to the common source extension.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2888-L2907
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2888-L2907

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

theorem QEC.Bounds.BPTCommutingProjectorModel.firstCutCoordinateTransport_conj_overlapLiftRight_CD_lift
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (P : Semantics.Operator
      (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))) :
    (M.firstCutCoordinateTransport region).conjOperator
      (overlapLiftRight
        (A := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region)) P) =
      M.fourFactorExtendCD region P := by sorry
