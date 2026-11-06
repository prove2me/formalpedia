-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutResidualTheta_scalar_compression_of_common_first_second_block
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCutResidualTheta_scalar_compression_of_common_first_second_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T15:09:58.880402+00:00
-- url     : https://prove2.me/theorems/2a34228c-04f6-46bd-8deb-519f75e5963e
-- title:
--   BPTCommuting Projector Model: second Cut Residual Theta scalar compression of common first second block
-- statement:
--   Scalar compression on `Theta tensor P_D` descends to the literal residual `Theta`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/ResidualScalar.lean#L35-L90
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/ResidualScalar.lean#L35-L90

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_ResidualProjection
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_ResidualScalar
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCutResidualTheta_scalar_compression_of_common_first_second_block
    {N C D : Type u}
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (eta : D) (heta : ‖eta‖ = 1) (P_D : Semantics.Operator D)
    (hP_D : P_D.IsSymmetricProjection) (hPeta : P_D eta = eta)
    (Qright : Semantics.Operator (Semantics.CompositeSystem N (Semantics.CompositeSystem C D)))
    (Theta Z : Semantics.Operator (Semantics.CompositeSystem N C))
    (hcommon : (tensorAssociatorUnitary N C D).symm.conjOperator Qright =
      TensorProduct.map Theta P_D)
    (hscalar : ∃ scalar : Complex,
      (tensorAssociatorUnitary N C D).symm.conjOperator Qright *
          TensorProduct.map Z (1 : Semantics.Operator D) *
          (tensorAssociatorUnitary N C D).symm.conjOperator Qright =
        scalar • (tensorAssociatorUnitary N C D).symm.conjOperator Qright) :
    ∃ scalar : Complex, Theta * Z * Theta = scalar • Theta := by sorry
