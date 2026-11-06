-- Prove2me | Theorems.Thm_QEC_Bounds_BPTEntropy_leftMarginal_codeCarrierPurification_toOperator
-- name    : QEC.Bounds.BPTEntropy.leftMarginal_codeCarrierPurification_toOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:27:48.008191+00:00
-- url     : https://prove2.me/theorems/84ecebd3-de05-48ae-9c1c-d6076ab129f4
-- title:
--   BPTEntropy: left Marginal code Carrier Purification to Operator
-- statement:
--   The carrier marginal of the purification is the maximally mixed carrier
--   state, allowing its entropy to be evaluated by the spectral API.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L748-L788
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L748-L788

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

theorem QEC.Bounds.BPTEntropy.leftMarginal_codeCarrierPurification_toOperator {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (C : QuantumCode H) (hdim : 0 < C.dimension) :
    (leftMarginal (pureDensity (codeCarrierPurificationVector C)
      (codeCarrierPurificationVector_normSq C hdim))).toOperator =
      ((C.dimension : Real)⁻¹ : Complex) • LinearMap.id := by sorry
