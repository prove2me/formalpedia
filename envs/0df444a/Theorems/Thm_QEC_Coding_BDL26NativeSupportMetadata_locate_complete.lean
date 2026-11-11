-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeSupportMetadata_locate_complete
-- name    : QEC.Coding.BDL26NativeSupportMetadata.locate_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:50:42.172295+00:00
-- url     : https://prove2.me/theorems/1309b493-70ac-433a-ba29-7ace2eada828
-- title:
--   BDL26 Native Support Metadata: locate complete
-- statement:
--   The BDL26 Native Support Metadata construction uses the locate complete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L42-L52
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L42-L52

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

theorem QEC.Coding.BDL26NativeSupportMetadata.locate_complete (c : Code) (L : List Code) (hc : c∈L) :
    ∃i,(locateQ c L).value=some i := by sorry
