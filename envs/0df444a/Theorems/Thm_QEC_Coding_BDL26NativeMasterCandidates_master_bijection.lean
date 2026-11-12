-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeMasterCandidates_master_bijection
-- name    : QEC.Coding.BDL26NativeMasterCandidates.master_bijection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:04:21.526918+00:00
-- url     : https://prove2.me/theorems/b36fa8f0-1198-4a47-92bb-83330e6a0df5
-- title:
--   BDL26 Native Master Candidates: master bijection
-- statement:
--   The BDL26 Native Master Candidates construction uses the master bijection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeMasterCandidates.lean#L735-L739
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeMasterCandidates.lean#L735-L739

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Mathlib.Data.List.Sublists
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeMasterCandidates
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeMasterCandidates
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
noncomputable section
open scoped Classical

theorem QEC.Coding.BDL26NativeMasterCandidates.master_bijection (S : OddScale) (n : ℕ) :
    (∀row,(masterEquiv S n).symm (masterEquiv S n row)=row) ∧
      (∀m,masterEquiv S n ((masterEquiv S n).symm m)=m) ∧
      ∀row,Rep S n row.val.1 (masterEquiv S n row) := by sorry
