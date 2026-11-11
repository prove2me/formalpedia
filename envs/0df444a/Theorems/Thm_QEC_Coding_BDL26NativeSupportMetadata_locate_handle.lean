-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeSupportMetadata_locate_handle
-- name    : QEC.Coding.BDL26NativeSupportMetadata.locate_handle
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T05:44:48.591378+00:00
-- url     : https://prove2.me/theorems/eec9cb89-d9ab-4467-acf3-bfb828398f1d
-- title:
--   BDL26 Native Support Metadata: locate handle
-- statement:
--   The BDL26 Native Support Metadata construction uses the locate handle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L89-L110
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L89-L110

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

theorem QEC.Coding.BDL26NativeSupportMetadata.locate_handle (c : Code) (L : List Code) (i : Fin L.length)
    (hi : (locateQ c L).value=some i) :
    (BDL26NativePresentationGenerator.handleQ c L).1=i.val := by sorry
