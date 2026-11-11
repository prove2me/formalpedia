-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeSupportMetadata_query_missing
-- name    : QEC.Coding.BDL26NativeSupportMetadata.query_missing
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T05:48:29.1234+00:00
-- url     : https://prove2.me/theorems/058dab45-ed16-46fc-afbc-93a4f530d9f6
-- title:
--   BDL26 Native Support Metadata: query missing
-- statement:
--   The BDL26 Native Support Metadata construction uses the query missing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L401-L406
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L401-L406

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

theorem QEC.Coding.BDL26NativeSupportMetadata.query_missing (S : OddScale) (n : ℕ) (codes : FourCodes)
    (hc : codes.first∉T S n) : (queryQ S n codes).value=none := by sorry
