-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeSupportMetadata_locate_missing
-- name    : QEC.Coding.BDL26NativeSupportMetadata.locate_missing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T05:42:40.366023+00:00
-- url     : https://prove2.me/theorems/2df470b8-0c13-49e4-b2ed-d151225aa640
-- title:
--   BDL26 Native Support Metadata: locate missing
-- statement:
--   The BDL26 Native Support Metadata construction uses the locate missing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L54-L65
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L54-L65

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

theorem QEC.Coding.BDL26NativeSupportMetadata.locate_missing (c : Code) (L : List Code) (hc : c∉L) :
    (locateQ c L).value=none ∧ (locateQ c L).operations=43*L.length+1 ∧
      (locateQ c L).allocations=0 := by sorry
