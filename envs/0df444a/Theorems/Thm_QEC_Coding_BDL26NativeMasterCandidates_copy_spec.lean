-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeMasterCandidates_copy_spec
-- name    : QEC.Coding.BDL26NativeMasterCandidates.copy_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:07:21.859844+00:00
-- url     : https://prove2.me/theorems/3420dd50-1571-4a54-a4ad-406e20cd9079
-- title:
--   BDL26 Native Master Candidates: copy spec
-- statement:
--   The BDL26 Native Master Candidates construction uses the copy spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeMasterCandidates.lean#L35-L39
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeMasterCandidates.lean#L35-L39

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

theorem QEC.Coding.BDL26NativeMasterCandidates.copy_spec (c : Code) :
    (copyCodeQ c).value=c ∧ (copyCodeQ c).operations=21 ∧
      (copyCodeQ c).allocations=1 := by sorry
