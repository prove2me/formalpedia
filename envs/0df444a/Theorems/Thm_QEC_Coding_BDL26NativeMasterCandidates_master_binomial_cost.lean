-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeMasterCandidates_master_binomial_cost
-- name    : QEC.Coding.BDL26NativeMasterCandidates.master_binomial_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:12:48.248607+00:00
-- url     : https://prove2.me/theorems/6900032b-16de-4f9d-874b-9b953afdc84c
-- title:
--   BDL26 Native Master Candidates: master binomial cost
-- statement:
--   The only hypotheses are local callback bounds; the closed top-level theorem
--   below derives them from the actual complete query, never from a caller budget.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeMasterCandidates.lean#L836-L860
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeMasterCandidates.lean#L836-L860

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

theorem QEC.Coding.BDL26NativeMasterCandidates.master_binomial_cost (S : OddScale) (n : ℕ) :
    let B := (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^15
    let A := (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^220
    let N := (actualCodes S n).length
    (masterCandidatesQ S n).operations≤A+
      Nat.choose N 4*(A+178*B^2+222*B+509)+
        4*(N+Nat.choose N 2+Nat.choose N 3)+1+N+Nat.choose N 2+2 ∧
      (masterCandidatesQ S n).allocations≤A+
        Nat.choose N 4*(A+4*B^2+8*B+36)+N+Nat.choose N 2+Nat.choose N 3+1 := by sorry
