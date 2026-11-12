-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeMasterCandidates_decoded_master_list
-- name    : QEC.Coding.BDL26NativeMasterCandidates.decoded_master_list
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:10:12.70801+00:00
-- url     : https://prove2.me/theorems/23271a77-0476-4533-8a02-9714b81e7a73
-- title:
--   BDL26 Native Master Candidates: decoded master list
-- statement:
--   The BDL26 Native Master Candidates construction uses the decoded master list property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeMasterCandidates.lean#L759-L767
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeMasterCandidates.lean#L759-L767

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

theorem QEC.Coding.BDL26NativeMasterCandidates.decoded_master_list (S : OddScale) (n : ℕ) :
    (decodedMasters S n).Nodup ∧ (decodedMasters S n).toFinset=Finset.univ := by sorry
