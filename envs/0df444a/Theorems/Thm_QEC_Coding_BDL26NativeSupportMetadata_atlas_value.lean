-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeSupportMetadata_atlas_value
-- name    : QEC.Coding.BDL26NativeSupportMetadata.atlas_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:23:19.966209+00:00
-- url     : https://prove2.me/theorems/0b5e417e-276e-4962-9ce1-8117bf58984f
-- title:
--   BDL26 Native Support Metadata: atlas value
-- statement:
--   The BDL26 Native Support Metadata construction uses the atlas value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L341-L343
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L341-L343

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

theorem QEC.Coding.BDL26NativeSupportMetadata.atlas_value (S : OddScale) (n : ℕ) :
    (atlasQ S n).value=(T S n).map (fun c => (c,(endpointQ (F S n) (V S n) (T S n) c).value)) := by sorry
