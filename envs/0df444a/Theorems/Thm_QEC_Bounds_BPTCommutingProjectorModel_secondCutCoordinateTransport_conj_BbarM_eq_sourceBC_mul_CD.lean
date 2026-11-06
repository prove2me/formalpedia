-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutCoordinateTransport_conj_BbarM_eq_sourceBC_mul_CD
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCutCoordinateTransport_conj_BbarM_eq_sourceBC_mul_CD
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T14:28:05.117531+00:00
-- url     : https://prove2.me/theorems/3ba6e4d7-a839-47e6-a4c3-695574d37c97
-- title:
--   BPTCommuting Projector Model: second Cut Coordinate Transport conj Bbar M eq source BC mul CD
-- statement:
--   The second-cut right overlap lift is the transported source `Pi_BC Pi_CD`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean#L332-L354
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean#L332-L354

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

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCutCoordinateTransport_conj_BbarM_eq_sourceBC_mul_CD
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.secondCutCoordinateTransport region).conjOperator
      (overlapLiftRight (A := M.fourFactorA region)
        (M.secondCutProjectorBbarM region)) =
      (M.fourFactorTransport region).conjOperator
        (M.projectorBC region * M.projectorCD region) := by sorry
