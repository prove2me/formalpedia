-- Prove2me | Theorems.Thm_QEC_Bounds_BPTEntropy_rightMarginal_codeCarrierPurification_eq_normalizedCodeProjector
-- name    : QEC.Bounds.BPTEntropy.rightMarginal_codeCarrierPurification_eq_normalizedCodeProjector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:27:41.270487+00:00
-- url     : https://prove2.me/theorems/6607a244-3a7d-4dcb-bdf7-84bb11a091c8
-- title:
--   BPTEntropy: right Marginal code Carrier Purification eq normalized Code Projector
-- statement:
--   The physical marginal of the carrier-reference purification is `Lambda`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L688-L732
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L688-L732

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

theorem QEC.Bounds.BPTEntropy.rightMarginal_codeCarrierPurification_eq_normalizedCodeProjector {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (C : QuantumCode H) (hdim : 0 < C.dimension) :
    rightMarginal (pureDensity (codeCarrierPurificationVector C)
      (codeCarrierPurificationVector_normSq C hdim)) = normalizedCodeProjector C hdim := by sorry
