-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeSupportMetadata_refresh_polynomial
-- name    : QEC.Coding.BDL26NativeSupportMetadata.refresh_polynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T08:09:24.583699+00:00
-- url     : https://prove2.me/theorems/b27fa089-e94c-4764-ae9a-af8203908b3f
-- title:
--   BDL26 Native Support Metadata: refresh polynomial
-- statement:
--   The complete initialized update has a polynomial bound in actual generator
--   size and the explicitly external finite trace length/weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L505-L524
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L505-L524

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

theorem QEC.Coding.BDL26NativeSupportMetadata.refresh_polynomial (S : OddScale) (n : ℕ) (codes : FourCodes)
    (table : BDL26NativeStateRows.Samples (Index S n))
    (trace : List (List (Index S n))) :
    let B := (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^15
    let A := (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^220
    (refreshEventQ S n codes table trace).operations≤
      2*A+180*B^2+269*B+410+2*trace.length+
        B*(2*BDL26NativeStateRows.traceWeight trace+11*trace.length) ∧
    (refreshEventQ S n codes table trace).allocations≤
      2*A+5*B^2+12*B+29+2*B*trace.length := by sorry
