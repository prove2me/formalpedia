-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeSupportMetadata_query_polynomial
-- name    : QEC.Coding.BDL26NativeSupportMetadata.query_polynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:53:03.110197+00:00
-- url     : https://prove2.me/theorems/26729938-a763-4fb1-9b8c-0c7d99df953b
-- title:
--   BDL26 Native Support Metadata: query polynomial
-- statement:
--   A closed polynomial in depth and the real generator radius. Every term
--   comes from the actual atlas/query loops and accepted generator bounds.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L422-L443
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L422-L443

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

theorem QEC.Coding.BDL26NativeSupportMetadata.query_polynomial (S : OddScale) (n : ℕ) (codes : FourCodes) :
    let B := (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^15
    let A := (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^220
    (queryQ S n codes).operations≤A+178*B^2+222*B+400 ∧
      (queryQ S n codes).allocations≤A+4*B^2+8*B+26 := by sorry
