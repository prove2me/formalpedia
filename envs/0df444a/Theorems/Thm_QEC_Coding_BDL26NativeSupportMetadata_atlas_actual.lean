-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeSupportMetadata_atlas_actual
-- name    : QEC.Coding.BDL26NativeSupportMetadata.atlas_actual
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T04:23:40.288346+00:00
-- url     : https://prove2.me/theorems/6dbb7c93-056a-4480-9412-c550bf875b0d
-- title:
--   BDL26 Native Support Metadata: atlas actual
-- statement:
--   The BDL26 Native Support Metadata construction uses the atlas actual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L601-L604
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L601-L604

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

theorem QEC.Coding.BDL26NativeSupportMetadata.atlas_actual (S : OddScale) (n : ℕ) (t : Triangle (P S n)) :
    (atlasReadQ (triangleCode S n t) (atlasQ S n).value).value=some (corners S n t) := by sorry
