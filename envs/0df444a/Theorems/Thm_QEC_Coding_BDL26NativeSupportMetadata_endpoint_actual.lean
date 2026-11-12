-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeSupportMetadata_endpoint_actual
-- name    : QEC.Coding.BDL26NativeSupportMetadata.endpoint_actual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:53:20.970196+00:00
-- url     : https://prove2.me/theorems/f24da34e-70dc-4c15-b31b-fb8c06a6894b
-- title:
--   BDL26 Native Support Metadata: endpoint actual
-- statement:
--   The BDL26 Native Support Metadata construction uses the endpoint actual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L572-L599
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L572-L599

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeStateRows
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeSupportMetadata
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open N
noncomputable section
open scoped Classical

theorem QEC.Coding.BDL26NativeSupportMetadata.endpoint_actual (S : OddScale) (n : ℕ) (t : Triangle (P S n)) :
    (endpointQ (F S n) (V S n) (T S n) (triangleCode S n t)).value=some (corners S n t) := by sorry
