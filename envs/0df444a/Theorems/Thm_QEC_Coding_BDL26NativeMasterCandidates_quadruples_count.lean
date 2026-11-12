-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeMasterCandidates_quadruples_count
-- name    : QEC.Coding.BDL26NativeMasterCandidates.quadruples_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:07:20.442323+00:00
-- url     : https://prove2.me/theorems/4a8fa4af-43a3-4a12-8986-677eb3185cdb
-- title:
--   BDL26 Native Master Candidates: quadruples count
-- statement:
--   The BDL26 Native Master Candidates construction uses the quadruples count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeMasterCandidates.lean#L148-L151
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeMasterCandidates.lean#L148-L151

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

theorem QEC.Coding.BDL26NativeMasterCandidates.quadruples_count {A : Type*} (L : List A) :
    (quadruples L).length=Nat.choose L.length 4 := by sorry
