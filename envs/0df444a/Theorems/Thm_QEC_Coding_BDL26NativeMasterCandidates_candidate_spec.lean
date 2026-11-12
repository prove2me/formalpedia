-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeMasterCandidates_candidate_spec
-- name    : QEC.Coding.BDL26NativeMasterCandidates.candidate_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:06:15.907193+00:00
-- url     : https://prove2.me/theorems/176ae9e0-253e-4209-a98c-e4ef7bbc4f5a
-- title:
--   BDL26 Native Master Candidates: candidate spec
-- statement:
--   The BDL26 Native Master Candidates construction uses the candidate spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeMasterCandidates.lean#L392-L400
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeMasterCandidates.lean#L392-L400

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

theorem QEC.Coding.BDL26NativeMasterCandidates.candidate_spec (S : OddScale) (n : ℕ) (a b c d : Code) :
    (candidateQ S n a b c d).value=
      (pack a b c d,(BDL26NativeSupportMetadata.queryQ S n (pack a b c d)).value) ∧
      (candidateQ S n a b c d).operations=
        (BDL26NativeSupportMetadata.queryQ S n (pack a b c d)).operations+100 ∧
      (candidateQ S n a b c d).allocations=
        (BDL26NativeSupportMetadata.queryQ S n (pack a b c d)).allocations+6 := by sorry
