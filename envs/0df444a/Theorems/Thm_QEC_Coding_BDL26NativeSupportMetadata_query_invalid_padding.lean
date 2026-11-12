-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeSupportMetadata_query_invalid_padding
-- name    : QEC.Coding.BDL26NativeSupportMetadata.query_invalid_padding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T08:09:58.617248+00:00
-- url     : https://prove2.me/theorems/252310d3-6aee-4a01-8992-8ad036ff5d38
-- title:
--   BDL26 Native Support Metadata: query invalid padding
-- statement:
--   The BDL26 Native Support Metadata construction uses the query invalid padding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L560-L565
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L560-L565

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

theorem QEC.Coding.BDL26NativeSupportMetadata.query_invalid_padding (S : OddScale) (n : ℕ) (codes : FourCodes)
    (hl : codes.first.l≠0) : (queryQ S n codes).value=none := by sorry
