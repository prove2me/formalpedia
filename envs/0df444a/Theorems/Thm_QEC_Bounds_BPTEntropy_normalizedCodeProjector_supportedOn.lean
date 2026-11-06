-- Prove2me | Theorems.Thm_QEC_Bounds_BPTEntropy_normalizedCodeProjector_supportedOn
-- name    : QEC.Bounds.BPTEntropy.normalizedCodeProjector_supportedOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:27:35.769432+00:00
-- url     : https://prove2.me/theorems/50bade6b-f6de-436a-88cc-4f414de8d231
-- title:
--   BPTEntropy: normalized Code Projector supported On
-- statement:
--   The normalized full-code-projector density has image in the code carrier.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L585-L591
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L585-L591

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

theorem QEC.Bounds.BPTEntropy.normalizedCodeProjector_supportedOn {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (C : QuantumCode H) (hdim : 0 < C.dimension) :
    DensityOperator.SupportedOn C (normalizedCodeProjector C hdim) := by sorry
