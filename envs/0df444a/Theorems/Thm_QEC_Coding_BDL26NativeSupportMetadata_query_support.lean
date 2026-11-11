-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeSupportMetadata_query_support
-- name    : QEC.Coding.BDL26NativeSupportMetadata.query_support
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T05:47:48.238859+00:00
-- url     : https://prove2.me/theorems/40b33b64-8dac-40e4-ad57-54637e6183ba
-- title:
--   BDL26 Native Support Metadata: query support
-- statement:
--   The BDL26 Native Support Metadata construction uses the query support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L323-L332
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L323-L332

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

theorem QEC.Coding.BDL26NativeSupportMetadata.query_support (S : OddScale) (n : ℕ) (codes : FourCodes)
    (U : List (Index S n)) (hU : (queryQ S n codes).value=some U) :
    U.Nodup ∧ U.length≤12 := by sorry
