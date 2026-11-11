-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeSupportMetadata_metadata_lengths
-- name    : QEC.Coding.BDL26NativeSupportMetadata.metadata_lengths
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:29:40.473746+00:00
-- url     : https://prove2.me/theorems/f1cb658e-b1d1-4b22-89db-5280bebee16a
-- title:
--   BDL26 Native Support Metadata: metadata lengths
-- statement:
--   These are actual retained list lengths, not a caller cardinality budget.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L409-L418
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L409-L418

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

theorem QEC.Coding.BDL26NativeSupportMetadata.metadata_lengths (S : OddScale) (n : ℕ) :
    let B := (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^15
    (T S n).length≤B ∧ (F S n).faces.length≤B ∧ (V S n).length≤B := by sorry
