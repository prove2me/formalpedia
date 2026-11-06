-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutResidualTheta_two_sided_scalar_compressions_for_noCloning
-- name    : QEC.Bounds.BPTCommutingProjectorModel.secondCutResidualTheta_two_sided_scalar_compressions_for_noCloning
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T15:10:30.695962+00:00
-- url     : https://prove2.me/theorems/d3ab9635-5f47-4491-b37b-c36da3cd0c98
-- title:
--   BPTCommuting Projector Model: second Cut Residual Theta two sided scalar compressions for no Cloning
-- statement:
--   The two residual erasures now act on one actual `Theta_{B'' C'}` while the
--   source complement projector `P_D` is retained.  This is the exact input to
--   the remaining two-factor no-cloning `finrank <= 1` closure.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/ResidualScalar.lean#L97-L132
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/ScalarCompression/ResidualScalar.lean#L97-L132

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

theorem QEC.Bounds.BPTCommutingProjectorModel.secondCutResidualTheta_two_sided_scalar_compressions_for_noCloning
    {N C D : Type u}
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (eta : D) (heta : ‖eta‖ = 1) (P_D : Semantics.Operator D)
    (hP_D : P_D.IsSymmetricProjection) (hPeta : P_D eta = eta)
    (Qright : Semantics.Operator (Semantics.CompositeSystem N (Semantics.CompositeSystem C D)))
    (Theta : Semantics.Operator (Semantics.CompositeSystem N C))
    (hcommon : (tensorAssociatorUnitary N C D).symm.conjOperator Qright =
      TensorProduct.map Theta P_D)
    (hinternal : ∀ X : Semantics.Operator N, ∃ scalar : Complex,
      (tensorAssociatorUnitary N C D).symm.conjOperator Qright *
          TensorProduct.map (TensorProduct.map X (1 : Semantics.Operator C))
            (1 : Semantics.Operator D) *
          (tensorAssociatorUnitary N C D).symm.conjOperator Qright =
        scalar • (tensorAssociatorUnitary N C D).symm.conjOperator Qright)
    (hexternal : ∀ Y : Semantics.Operator C, ∃ scalar : Complex,
      (tensorAssociatorUnitary N C D).symm.conjOperator Qright *
          TensorProduct.map (TensorProduct.map (1 : Semantics.Operator N) Y)
            (1 : Semantics.Operator D) *
          (tensorAssociatorUnitary N C D).symm.conjOperator Qright =
        scalar • (tensorAssociatorUnitary N C D).symm.conjOperator Qright) :
    (∀ X : Semantics.Operator N, ∃ scalar : Complex,
      Theta * TensorProduct.map X (1 : Semantics.Operator C) * Theta = scalar • Theta) ∧
    (∀ Y : Semantics.Operator C, ∃ scalar : Complex,
      Theta * TensorProduct.map (1 : Semantics.Operator N) Y * Theta = scalar • Theta) := by sorry
