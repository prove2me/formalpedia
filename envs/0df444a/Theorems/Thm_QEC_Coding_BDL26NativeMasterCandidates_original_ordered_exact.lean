-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeMasterCandidates_original_ordered_exact
-- name    : QEC.Coding.BDL26NativeMasterCandidates.original_ordered_exact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:11:03.84332+00:00
-- url     : https://prove2.me/theorems/d07059a6-e1de-4727-ab2e-2b6325966d50
-- title:
--   BDL26 Native Master Candidates: original ordered exact
-- statement:
--   The BDL26 Native Master Candidates construction uses the original ordered exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeMasterCandidates.lean#L783-L797
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeMasterCandidates.lean#L783-L797

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

theorem QEC.Coding.BDL26NativeMasterCandidates.original_ordered_exact (S : OddScale) (n : ℕ) (J : Vertex (P S n) → Space) (r : ℝ) :
    originalOrderedEvents S n J r=
      (Finset.univ : Finset (Event (P S n) J r)).sort (eventPriorityLE (P S n) J r) := by sorry
