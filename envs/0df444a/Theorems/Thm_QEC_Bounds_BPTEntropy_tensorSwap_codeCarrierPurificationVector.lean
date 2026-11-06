-- Prove2me | Theorems.Thm_QEC_Bounds_BPTEntropy_tensorSwap_codeCarrierPurificationVector
-- name    : QEC.Bounds.BPTEntropy.tensorSwap_codeCarrierPurificationVector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:27:41.196039+00:00
-- url     : https://prove2.me/theorems/3c5b6b34-5e34-4648-bc89-318f6b5735e4
-- title:
--   BPTEntropy: tensor Swap code Carrier Purification Vector
-- statement:
--   Swapping the carrier purification puts the code carrier on the left.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L735-L744
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L735-L744

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

theorem QEC.Bounds.BPTEntropy.tensorSwap_codeCarrierPurificationVector {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (C : QuantumCode H) :
    tensorSwap H C.carrier (codeCarrierPurificationVector C) =
      ∑ i : Fin C.dimension,
        (stdOrthonormalBasis Complex C.carrier i) ⊗ₜ[Complex]
          ((Real.sqrt ((C.dimension : Real)⁻¹) : Complex) •
            ((stdOrthonormalBasis Complex C.carrier i : C.carrier) : H)) := by sorry
