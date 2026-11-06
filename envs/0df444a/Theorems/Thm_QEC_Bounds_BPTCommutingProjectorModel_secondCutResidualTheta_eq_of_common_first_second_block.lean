-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutResidualTheta_eq_of_common_first_second_block
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCutResidualTheta_eq_of_common_first_second_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T15:09:13.796116+00:00
-- url     : https://prove2.me/theorems/3211ed83-7859-459d-9ea5-80904c837c0d
-- title:
--   BPTCommuting Projector Model: second Cut Residual Theta eq of common first second block
-- statement:
--   The literal residual compression recovers `Theta` from `Theta tensor P_D`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/ResidualProjection.lean#L64-L77
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/ResidualProjection.lean#L64-L77

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_Tensor
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_ResidualProjection
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCutResidualTheta_eq_of_common_first_second_block
    {N C D : Type u}
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (eta : D) (heta : ‖eta‖ = 1) (P_D : Semantics.Operator D) (hPeta : P_D eta = eta)
    (Qright : Semantics.Operator (Semantics.CompositeSystem N (Semantics.CompositeSystem C D)))
    (Theta : Semantics.Operator (Semantics.CompositeSystem N C))
    (hcommon : (tensorAssociatorUnitary N C D).symm.conjOperator Qright =
      TensorProduct.map Theta P_D) :
    secondCutResidualTheta eta Qright = Theta := by sorry
