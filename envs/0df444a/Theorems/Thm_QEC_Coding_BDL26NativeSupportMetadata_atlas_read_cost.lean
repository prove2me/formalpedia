-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeSupportMetadata_atlas_read_cost
-- name    : QEC.Coding.BDL26NativeSupportMetadata.atlas_read_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:30:15.508177+00:00
-- url     : https://prove2.me/theorems/44dcfe6b-382e-4568-9d92-a956e52ee99a
-- title:
--   BDL26 Native Support Metadata: atlas read cost
-- statement:
--   The BDL26 Native Support Metadata construction uses the atlas read cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L203-L213
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L203-L213

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

theorem QEC.Coding.BDL26NativeSupportMetadata.atlas_read_cost {A : Type*} (c : Code) (L : List (Code × Option A)) :
    (atlasReadQ c L).operations≤43*L.length+1 ∧ (atlasReadQ c L).allocations=0 := by sorry
