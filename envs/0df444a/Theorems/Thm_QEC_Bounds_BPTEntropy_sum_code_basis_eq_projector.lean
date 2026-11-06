-- Prove2me | Theorems.Thm_QEC_Bounds_BPTEntropy_sum_code_basis_eq_projector
-- name    : QEC.Bounds.BPTEntropy.sum_code_basis_eq_projector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:48:12.534572+00:00
-- url     : https://prove2.me/theorems/1acd1997-38f8-4fa6-bc56-a7a74adde699
-- title:
--   BPTEntropy: sum code basis eq projector
-- statement:
--   The code-basis resolution of the full-code projector.  This turns the
--   normalized projector into a concrete finite density operator below.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L433-L466
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L433-L466

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Semantics_Entropy_Subadditivity
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open scoped TensorProduct
open QEC.Bounds.BPTEntropy
open Semantics
open Semantics.DensityOperator
universe u

theorem QEC.Bounds.BPTEntropy.sum_code_basis_eq_projector {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (C : QuantumCode H) :
    ∑ i : Fin C.dimension,
      (InnerProductSpace.rankOne Complex
        ((stdOrthonormalBasis Complex C.carrier i : C.carrier) : H)
        ((stdOrthonormalBasis Complex C.carrier i : C.carrier) : H)).toLinearMap =
      C.projector := by sorry
