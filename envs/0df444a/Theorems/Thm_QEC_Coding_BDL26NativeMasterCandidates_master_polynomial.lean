-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeMasterCandidates_master_polynomial
-- name    : QEC.Coding.BDL26NativeMasterCandidates.master_polynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:13:25.070933+00:00
-- url     : https://prove2.me/theorems/fb8ad39e-778d-476a-9ae6-be2dbf5fde4a
-- title:
--   BDL26 Native Master Candidates: master polynomial
-- statement:
--   Closed cost of the actual complete interpreter, including repeated setup
--   at all choose(N,4) leaves and all three append copies per emitted row.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeMasterCandidates.lean#L864-L902
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeMasterCandidates.lean#L864-L902

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Mathlib.Data.List.Sublists
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeMasterCandidates
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeMasterCandidates
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
noncomputable section
open scoped Classical

theorem QEC.Coding.BDL26NativeMasterCandidates.master_polynomial (S : OddScale) (n : ℕ) :
    let B := (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^15
    let A := (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^220
    (masterCandidatesQ S n).operations≤
      A+(B+1)^4*(A+178*B^2+222*B+509)+13*(B+1)^3+2 ∧
      (masterCandidatesQ S n).allocations≤
        A+(B+1)^4*(A+4*B^2+8*B+36)+3*(B+1)^3+1 := by sorry
