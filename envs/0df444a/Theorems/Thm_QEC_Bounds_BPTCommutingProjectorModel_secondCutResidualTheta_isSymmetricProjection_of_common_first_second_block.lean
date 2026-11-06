-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutResidualTheta_isSymmetricProjection_of_common_first_second_block
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCutResidualTheta_isSymmetricProjection_of_common_first_second_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T15:10:12.320977+00:00
-- url     : https://prove2.me/theorems/eb8435c6-6788-47d9-a3bf-188dbcf07235
-- title:
--   BPTCommuting Projector Model: second Cut Residual Theta is Symmetric Projection of common first second block
-- statement:
--   The general source block `Theta tensor P_D` transfers projection structure to `Theta`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/ResidualProjection.lean#L134-L156
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/ResidualProjection.lean#L134-L156

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

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCutResidualTheta_isSymmetricProjection_of_common_first_second_block
    {N C D : Type u}
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (eta : D) (heta : ‖eta‖ = 1) (P_D : Semantics.Operator D)
    (hP_D : P_D.IsSymmetricProjection) (hP_D0 : P_D ≠ 0) (hPeta : P_D eta = eta)
    (Qright : Semantics.Operator (Semantics.CompositeSystem N (Semantics.CompositeSystem C D)))
    (Theta : Semantics.Operator (Semantics.CompositeSystem N C))
    (hQright : Qright.IsSymmetricProjection)
    (hcommon : (tensorAssociatorUnitary N C D).symm.conjOperator Qright =
      TensorProduct.map Theta P_D) :
    (secondCutResidualTheta eta Qright).IsSymmetricProjection := by sorry
