-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutCoordinateTransport_conj_overlapLiftRight_BbarM
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCutCoordinateTransport_conj_overlapLiftRight_BbarM
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:21:32.543412+00:00
-- url     : https://prove2.me/theorems/653d7644-e9ec-4600-bda7-780c59ae429d
-- title:
--   BPTCommuting Projector Model: second Cut Coordinate Transport conj overlap Lift Right Bbar M
-- statement:
--   The literal second-cut right overlap lift is exactly the product of the
--   source `BC` and `CD` factors in common four-factor coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean#L229-L255
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean#L229-L255

import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Selection
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCutCoordinateTransport_conj_overlapLiftRight_BbarM
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.secondCutCoordinateTransport region).conjOperator
      (overlapLiftRight (A := M.fourFactorA region)
        (M.secondCutProjectorBbarM region)) =
      M.fourFactorExtendBC region (M.fourFactorProjectorBCLocal region) *
        M.fourFactorExtendCD region (M.fourFactorProjectorCDLocal region) := by sorry
